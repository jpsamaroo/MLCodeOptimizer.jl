module MLCodeOptimizer

import Core: CodeInfo
const CC = Core.Compiler
import .CC: IRCode
import Core.Compiler: EscapeAnalysis
const EA = EscapeAnalysis

import InteractiveUtils

include("finalizer-elision.jl")

const MY_CI = Ref{CodeInfo}()
const MY_IR = Ref{IRCode}()

abstract type AbstractConstraint end

struct FinalizerInlined{T} <: AbstractConstraint end

struct ConstraintSet
    cons::Vector{AbstractConstraint}
end
ConstraintSet() = ConstraintSet(AbstractConstraint[])

# Copied from https://gist.github.com/aviatesk/9b247e5e64f78454a70c3ec94c1ab2ad
import Core: MethodMatch
import .CC: _methods_by_ftype, InferenceParams, get_world_counter, MethodInstance,
    specialize_method, InferenceResult, typeinf, InferenceState, NativeInterpreter,
    code_cache

function invoke_in_absint(f, interp, opt_cb, args...)
    @nospecialize f args
    tt = Base.signature_type(f, Tuple{map(Core.Typeof, args)...})
    mm = get_single_method_match(tt, InferenceParams(interp).MAX_METHODS, get_world_counter(interp))
    mi = specialize_method(mm.method, mm.spec_types, mm.sparams)::MethodInstance
    code = Core.Compiler.get(code_cache(interp), mi, nothing)
    if code !== nothing
        inf = code.inferred::Vector{UInt8}
        ci = Base._uncompressed_ir(code, inf)
        return Core.OpaqueClosure(ci)
    end
    result = InferenceResult(mi)
    frame = InferenceState(result, #=cache=# :global, interp)
    typeinf(interp, frame)
    ci = frame.src
    ci = opt_cb(interp, ci)
    return Core.OpaqueClosure(ci)
end

function get_single_method_match(@nospecialize(tt), lim, world)
    mms = _methods_by_ftype(tt, lim, world)
    isa(mms, Bool) && single_match_error(tt)
    local mm = nothing
    for i = 1:length(mms)
        mmᵢ = mms[i]::MethodMatch
        if tt === mmᵢ.spec_types
            mm === nothing || single_match_error(tt)
            mm = mmᵢ
        end
    end
    mm isa MethodMatch || single_match_error(tt)
    return mm
end

function optimize(interp, ci::CodeInfo)
    @show ci
    MY_CI[] = ci

    # Construct interpreter and states
    opt_params = CC.OptimizationParams(interp)
    mi = ci.parent::MethodInstance
    opt_state = CC.OptimizationState(mi, opt_params, interp)
    nargs = let def = opt_state.linfo.def; isa(def, Method) ? Int(def.nargs) : 0; end
    cc = CC.code_cache(interp)
    ipo_cache = CC.ipo_escape_cache(cc)
    caller = CC.InferenceResult(mi)

    # Run default optimizations and get the IRCode
    ir = CC.run_passes(ci, opt_state, caller)

    @show ir

    # Run IPO EA
    estate = EA.analyze_escapes(ir, nargs, #=call_resolved=#false, ipo_cache)
    CC.cache_escapes!(caller, estate)
    ae = caller.argescapes

    # Perform finalizer elision
    domtree = CC.construct_domtree(ir.cfg.blocks)
    # FIXME
    #ir = early_finalize!(ir, estate, domtree, interp)

    # Finalize IR
    CC.finish(interp, opt_state, opt_params, ir, caller)

    MY_IR[] = ir
    @show ir

    @assert opt_state.ir === ir
    return CC.ir_to_codeinf!(opt_state)::CodeInfo
end

function execute!(f, #=constraints::ConstraintSet,=# args...)
    @nospecialize f args
    # FIXME: Add caching
    interp = NativeInterpreter(get_world_counter())
    oc = invoke_in_absint(f, interp, optimize, args...)
    return oc(args...)
end

end # module MLCodeOptimizer
