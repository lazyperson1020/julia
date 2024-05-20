// This file is a part of Julia. License is MIT: https://julialang.org/license

#include "julia.h"
#include "julia_internal.h"

jl_value_t *jl_fptr_const_opaque_closure(jl_opaque_closure_t *oc, jl_value_t **args, size_t nargs)
{
    return oc->captures;
}

jl_value_t *jl_fptr_const_opaque_closure_typeerror(jl_opaque_closure_t *oc, jl_value_t **args, size_t nargs)
{
    jl_type_error("OpaqueClosure", jl_tparam1(jl_typeof(oc)), oc->captures);
}

// determine whether `argt` is a valid argument type tuple for the given opaque closure method
JL_DLLEXPORT int jl_is_valid_oc_argtype(jl_tupletype_t *argt, jl_method_t *source)
{
    if (!source->isva) {
        if (jl_is_va_tuple(argt))
            return 0;
        if (jl_nparams(argt)+1 > source->nargs)
            return 0;
    }
    if (jl_nparams(argt) + 1 - jl_is_va_tuple(argt) < source->nargs - source->isva)
        return 0;
    return 1;
}


JL_DLLEXPORT jl_opaque_closure_t *jl_new_opaque_closure_from_code_info(jl_tupletype_t *argt, jl_value_t *rt_lb, jl_value_t *rt_ub,
    jl_module_t *mod, jl_code_info_t *ci, int lineno, jl_value_t *file, int nargs, int isva, jl_value_t *env, int do_compile, int isinferred)
{
    jl_value_t *root = NULL, *sigtype = NULL;
    jl_code_instance_t *inst = NULL;
    JL_GC_PUSH3(&root, &sigtype, &inst);
    root = jl_box_long(lineno);
    root = jl_new_struct(jl_linenumbernode_type, root, file);
    jl_method_t *meth = jl_make_opaque_closure_method(mod, jl_nothing, nargs, root, ci, isva, isinferred);
    root = (jl_value_t*)meth;
    size_t world = jl_current_task->world_age;
    // these are only legal in the current world since they are not in any tables
    jl_atomic_store_release(&meth->primary_world, world);
    jl_atomic_store_release(&meth->deleted_world, world);

    if (isinferred) {
        sigtype = jl_argtype_with_function(env, (jl_value_t*)argt);
        jl_method_instance_t *mi = jl_specializations_get_linfo((jl_method_t*)root, sigtype, jl_emptysvec);
        inst = jl_new_codeinst(mi, jl_nothing, rt_ub, (jl_value_t*)jl_any_type, NULL, (jl_value_t*)ci,
            0, world, world, 0, 0, jl_nothing, 0, ci->debuginfo);
        jl_mi_cache_insert(mi, inst);
    }

    jl_opaque_closure_t *oc = jl_new_opaque_closure(argt, rt_lb, rt_ub, root, env, world, do_compile);
    JL_GC_POP();
    return oc;
}

JL_CALLABLE(jl_new_opaque_closure_jlcall)
{
    if (nargs < 4)
        jl_error("new_opaque_closure: Not enough arguments");
    jl_value_t *captures = jl_f_tuple(NULL, args + 4, nargs - 4);
    JL_GC_PUSH1(&captures);
    jl_value_t* oc = (jl_value_t*)jl_new_opaque_closure((jl_tupletype_t*)args[0],
        args[1], args[2], args[3], captures, jl_current_task->world_age, /* do_compile */ 1);
    JL_GC_POP();
    return oc;
}

jl_opaque_closure_t *jl_new_opaque_closure(jl_tupletype_t *argt, jl_value_t *rt_lb, jl_value_t *rt_ub,
    jl_value_t *source_, jl_value_t *captures, size_t world, int do_compile)
{
    if (!jl_is_tuple_type((jl_value_t*)argt)) {
        jl_error("OpaqueClosure argument tuple must be a tuple type");
    }
    JL_TYPECHK(new_opaque_closure, type, rt_lb);
    JL_TYPECHK(new_opaque_closure, type, rt_ub);
    JL_TYPECHK(new_opaque_closure, method, source_);
    jl_method_t *source = (jl_method_t*)source_;
    if (!source->isva) {
        if (jl_is_va_tuple(argt))
            jl_error("Argument type tuple is vararg but method is not");
        if (jl_nparams(argt)+1 > source->nargs)
            jl_error("Argument type tuple has too many required arguments for method");
    }
    if (jl_nparams(argt) + 1 - jl_is_va_tuple(argt) < source->nargs - source->isva)
        jl_error("Argument type tuple has too few required arguments for method");
    jl_value_t *sigtype = NULL;
    jl_code_instance_t *ci = NULL;
    JL_GC_PUSH2(&sigtype, &ci);
    sigtype = jl_argtype_with_function(captures, (jl_value_t*)argt);

    jl_method_instance_t *mi = jl_specializations_get_linfo(source, sigtype, jl_emptysvec);
    int compile_option = jl_options.compile_enabled;
    // disabling compilation per-module can override global setting
    int mod_setting = jl_get_module_compile(source->module);
    if (mod_setting == JL_OPTIONS_COMPILE_OFF || mod_setting == JL_OPTIONS_COMPILE_MIN)
        compile_option = source->module->compile;
    
    if (compile_option == JL_OPTIONS_COMPILE_OFF || compile_option == JL_OPTIONS_COMPILE_MIN) {
        // TODO: Check for disabled compilation
    }

    jl_fptr_args_t invoke = (jl_fptr_args_t)jl_interpret_opaque_closure;
    void *specptr = NULL;

    // Ok, compilation is enabled. We'll need to try to compile something (probably).
    // Try to find a codeinst we have already inferred (e.g. while we were compiling
    // something else).
    ci = jl_method_compiled(mi, world);
    if (!ci && do_compile) {
        JL_LOCK(&jl_codegen_lock);

        // We need to compile (and probably also type-infer)
        ci = jl_method_inferred_with_abi(mi, world);
        if (!ci)
            ci = jl_type_infer(mi, world, 0, SOURCE_MODE_FORCE_SOURCE_UNCACHED);

        if (ci) {
            // We need to compile, fix-up return type first
            if (jl_atomic_load_acquire(&ci->invoke) == jl_fptr_const_return) {
                jl_atomic_store_release(&ci->invoke, NULL);
            }
            if (!jl_subtype(rt_lb, ci->rettype)) {
                jl_value_t *ts[2] = {rt_lb, (jl_value_t*)ci->rettype};
                ci->rettype = jl_type_union(ts, 2);
            }
            if (!jl_subtype(ci->rettype, rt_ub)) {
                ci->rettype = jl_type_intersection(rt_ub, ci->rettype);
            }

            fprintf(stderr, "Got inferred after inference: %p\n", jl_atomic_load_relaxed(&ci->inferred));
            assert(jl_atomic_load_acquire(&ci->invoke) == NULL);

            int did_compile = jl_compile_codeinst(ci);
            if (jl_atomic_load_relaxed(&ci->invoke) == NULL) {
                fprintf(stderr, "No invoke after codegen\n");
                assert(0);
                // Something went wrong. Bail to the fallback path.
                ci = NULL;
            } else {
                assert(jl_atomic_load_relaxed(&ci->specptr.fptr) != NULL);
                jl_atomic_store_release(&ci->max_world, -1); // TODO: This is cheating...
                fprintf(stderr, "Got invoke after codegen: %p\n", jl_atomic_load_relaxed(&ci->specptr.fptr));
                if (did_compile)
                    jl_record_precompile_statement(mi);
                jl_mi_cache_insert(mi, ci);
            }
        }
        JL_UNLOCK(&jl_codegen_lock);
    }
    if (ci) {
        invoke = (jl_fptr_args_t)jl_atomic_load_relaxed(&ci->invoke);
        specptr = jl_atomic_load_relaxed(&ci->specptr.fptr);
        fprintf(stderr, "Got specptr: %p\n", specptr);
    }

    if (invoke == (jl_fptr_args_t) jl_fptr_interpret_call) {
        invoke = (jl_fptr_args_t)jl_interpret_opaque_closure;
    }
    else if (invoke == (jl_fptr_args_t)jl_fptr_args) {
        assert(specptr != NULL);
        invoke = (jl_fptr_args_t)specptr;
    }
    // TODO: Add proper support for shared const ABI functions across OpaqueClosures
    assert(invoke != (jl_fptr_args_t)jl_fptr_const_return);
    // TODO: Support sparams
    assert(invoke != (jl_fptr_args_t)jl_fptr_sparam);

    jl_value_t *oc_type JL_ALWAYS_LEAFTYPE = jl_apply_type2((jl_value_t*)jl_opaque_closure_type, (jl_value_t*)argt, ci != NULL ? ci->rettype : rt_ub);
    JL_GC_PROMISE_ROOTED(oc_type);

    if (!specptr) {
        fprintf(stderr, "Generic fallback for OpaqueClosure\n");

        sigtype = jl_argtype_with_function_type((jl_value_t*)oc_type, (jl_value_t*)argt);
        jl_method_instance_t *mi_generic = jl_specializations_get_linfo(jl_opaque_closure_method, sigtype, jl_emptysvec);

        // OC wrapper methods are not world dependent
        ci = jl_get_method_inferred(mi_generic, ci != NULL ? ci->rettype : rt_ub, 1, ~(size_t)0, NULL);
        if (!jl_atomic_load_acquire(&ci->invoke))
            jl_compile_codeinst(ci);
        specptr = jl_atomic_load_relaxed(&ci->specptr.fptr);
    }

    jl_opaque_closure_t *oc = (jl_opaque_closure_t*)jl_gc_alloc(jl_current_task->ptls, sizeof(jl_opaque_closure_t), oc_type);
    oc->source = source;
    oc->captures = captures;
    oc->world = world;
    oc->invoke = invoke;
    oc->specptr = specptr;

    JL_GC_POP();
    return oc;
}

// check whether the specified number of arguments is compatible with the
// specified number of parameters of the tuple type
int jl_tupletype_length_compat(jl_value_t *v, size_t nargs)
{
    v = jl_unwrap_unionall(v);
    assert(jl_is_tuple_type(v));
    size_t nparams = jl_nparams(v);
    if (nparams == 0)
        return nargs == 0;
    jl_value_t *va = jl_tparam(v,nparams-1);
    if (jl_is_vararg(va)) {
        jl_value_t *len = jl_unwrap_vararg_num(va);
        if (len &&jl_is_long(len))
            return nargs == nparams - 1 + jl_unbox_long(len);
        return nargs >= nparams - 1;
    }
    return nparams == nargs;
}

JL_CALLABLE(jl_f_opaque_closure_call)
{
    jl_opaque_closure_t* oc = (jl_opaque_closure_t*)F;
    jl_value_t *argt = jl_tparam0(jl_typeof(oc));
    if (!jl_tupletype_length_compat(argt, nargs))
        jl_method_error(F, args, nargs + 1, oc->world);
    argt = jl_unwrap_unionall(argt);
    assert(jl_is_datatype(argt));
    jl_svec_t *types = jl_get_fieldtypes((jl_datatype_t*)argt);
    size_t ntypes = jl_svec_len(types);
    for (int i = 0; i < nargs; ++i) {
        jl_value_t *typ = i >= ntypes ? jl_svecref(types, ntypes-1) : jl_svecref(types, i);
        if (jl_is_vararg(typ))
            typ = jl_unwrap_vararg(typ);
        jl_typeassert(args[i], typ);
    }
    return oc->invoke(F, args, nargs);
}
