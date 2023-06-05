import .CC: AbstractInterpreter, IRCode, DomTree
import .EA: EscapeState, EscapeInfo

const EARLY_FINALIZE_VERBOSE = Ref(false)

function early_finalize!(ir::IRCode, estate::EscapeState, domtree::DomTree, interp::AbstractInterpreter)
    EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int), "early_finalize!: Analyzing with nargs %d\n", estate.nargs)
    # Find all allocations that escape only through a finalizer
    isalloc(ir::IRCode, pc::Int) = isexpr(ir.stmts[pc][:inst], :new)
    to_finalize = Pair{Int,EscapeInfo}[]
    if length(estate.escapes) != estate.nargs+length(ir.stmts)
        #=EARLY_FINALIZE_VERBOSE[] &&=# ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int, Int), "early_finalize!: Mismatched stmts (%d) with escape infos (%d)\n", length(ir.stmts), length(estate.escapes))
    end
    for idx in (estate.nargs+1):length(estate.escapes)
        info = estate.escapes[idx]
        pc = idx - estate.nargs
        if pc > length(ir.stmts)
            # FIXME
            continue
        end
        if has_finalizer_escape(info) && isalloc(ir, pc)
            EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int), "early_finalize!: Found finalizing alloc at %d\n", pc)
            push!(to_finalize, pc => info)
        end
    end

    for (alloc_idx, alloc_info) in to_finalize
        for pc in 1:length(ir.stmts)
            inst = ir.stmts[pc][:inst]
            if isexpr(inst, :invoke)
                mi = inst.args[1]::MethodInstance
                for argidx in 2:length(inst.args)
                    arg = inst.args[argidx]
                    if arg isa SSAValue && arg.id == alloc_idx
                        println("Possible ArgEscape:")
                        println(inst)
                        cc = code_cache(interp)
                        if haskey(cc, mi)
                            ae = code_cache(interp)[mi].argescapes
                            if ae !== nothing
                                ae::ArgEscapeCache
                                println("FOUND ESCAPE")
                                println(length(ae.argescapes))
                                for ae_info in ae.argescapes
                                #ae_info = ae.argescapes[argidx] # Skip func arg
                                    println(ae_info)
                                end
                            end
                        end
                    end
                end
            end
        end
    end

    # Find all locations to insert calls to `finalize`
    # Currently this is just all returns and unreachables
    return_locs = Int[]
    for bb in ir.cfg.blocks
        inst = ir.stmts.inst[bb.stmts.stop]
        if inst isa ReturnNode
            if isdefined(inst, :val)
                EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int), "early_finalize!: Found return at %d\n", bb.stmts.stop)
                push!(return_locs, bb.stmts.stop)
            else
                # Unreachable, try to find `Base.throw` one insn before
                block = ir.cfg.blocks[block_for_inst(ir, bb.stmts.stop)]
                throw_pc = bb.stmts.stop - 1
                if throw_pc in block.stmts
                    EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int), "early_finalize!: Found throw at %d\n", throw_pc)
                    push!(return_locs, throw_pc)
                end
            end
        end
    end

    # Insert `finalize` calls in order
    for idx in return_locs
        non_escaping = Pair{Int,EscapeInfo}[]
        for (alloc_idx, alloc_info) in to_finalize
            # Check if this allocation is otherwise unescaping at this return
            EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int, Int, Bool, Bool, Bool),
                                              "early_finalize!: For alloc at %d, return at %d: ReturnEscape(%d), ArgEscape(%d), ThrownEscape(%d)\n",
                                              alloc_idx, idx, has_return_escape(alloc_info, idx), has_arg_escape(alloc_info), has_thrown_escape(alloc_info, idx))
            if has_return_escape(alloc_info, idx) ||
               has_arg_escape(alloc_info) ||
               has_thrown_escape(alloc_info, idx)
                continue
            end
            # TODO: Check if the argescape is truly escaping
            # Construct all blocks for which the allocation is live
            allblocks = Int[]
            fdu = FieldDefUse()
            for pc in alloc_info.Liveness
                pc < 1 && continue
                if !(1 <= pc <= length(ir.stmts))
                    ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int, Int, Int),
                          "early_finalize!: pc (%d) out-of-bounds (1:%d), nargs %d\n",
                          pc, length(ir.stmts), estate.nargs)
                    continue
                end
                EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int, Int, Int), "early_finalize!: For alloc at %d, return at %d, value is live at %d\n", alloc_idx, idx, pc)
                push!(fdu.defs, pc)
                push!(allblocks, block_for_inst(ir, pc))
            end
            # Add this allocation if there is any valid def-use pair
            # N.B. not necessary: `push!(fdu.uses, idx)`
            use = idx
            defs = find_def_for_use(ir, domtree, allblocks, fdu, use)
            EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int, Int, Bool),
                                              "early_finalize!: For alloc at %d, return at %d: Defs(%d)\n",
                                              alloc_idx, idx, defs !== nothing ? defs[1] : -1)
            if defs !== nothing && defs[1] == alloc_idx
                push!(non_escaping, alloc_idx=>alloc_info)
            end
        end
        if length(non_escaping) > 0
            ct_expr = Expr(:foreigncall, :(:jl_get_current_task), Ref{Task}, svec(), 0, :(:ccall))
            ct_insn = NewInstruction(ct_expr, Ref{Task})
            ct = insert_node!(ir, idx, ct_insn)
            for (alloc_idx, alloc_info) in non_escaping
                EARLY_FINALIZE_VERBOSE[] && ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int, Int), "early_finalize!: For alloc at %d, return at %d, inserting finalize\n", alloc_idx, idx)
                fin_expr = Expr(:foreigncall, :(:jl_finalize_th), Nothing, svec(Any, Any), 0, :(:ccall), ct, SSAValue(alloc_idx))
                fin_insn = NewInstruction(fin_expr, Nothing)
                fin = insert_node!(ir, idx, fin_insn)
            end
        end
    end

    return ir
end
