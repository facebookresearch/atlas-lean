---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.W_complete
---

# Completeness of Algorithm W

**Completeness of Algorithm W** (Damas-Milner): if the free variables of `Γ` are below
`n` and some instance `u Γ` types `e` with `τ'`, then W succeeds, and there is `r` with
`u = s ≫ r` on the variables below `n` and `τ' = τ.subst r`.

## Depends on

- [Ctx](../typing/part-01/ctx.md)
- [Ftv](../typing/part-01/ftv.md)
- [Subst](../typing/part-01/subst.md)
- [Expr](../typing/part-01/expr.md)
- [Has Type](../typing/part-01/has-type.md)
- [Ty](../typing/part-01/ty.md)
- [W](../algorithm-w/w.md)
- [Subst](../../../unification/basic/part-01/subst.md)
- [Term](../../../unification/basic/part-01/term.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)

## Proof depends on

- [Cons](../typing/part-02/cons.md)
- [Of lookup eq](../typing/part-02/of-lookup-eq.md)
- [Ftv congr](../typing/part-01/ftv-congr.md)
- [Lookup](../typing/part-01/lookup.md)
- [Lookup subst congr](../typing/part-01/lookup-subst-congr.md)
- [Visible Vars](../typing/part-01/visible-vars.md)
- [Generality](../typing/part-02/mono.md)
- [Scheme](../typing/part-01/scheme.md)
- [More General](../typing/part-01/more-general.md)
- [Bound Sup](../algorithm-w/bound-sup.md)
- [Eval](../typing/part-01/eval.md)
- [Inst](../typing/part-01/inst.md)
- [Subst Ty](../typing/part-01/subst-ty.md)
- [Vars Below](vars-below.md)
- [Freshness](w-fresh.md)
- [Gen](../typing/part-01/gen.md)
- [Gen congr](gen-congr.md)
- [Substitution lemma](../typing/part-02/has-type-var-iff.md)
- [Subst Ty gen more General](subst-ty-gen-more-general.md)
- [To Scheme](../typing/part-01/to-scheme.md)
- [Equations](../../../unification/basic/part-01/equations.md)
- [Comp](../../../unification/basic/part-01/comp.md)
- [Exists of mem vars subst](../../../unification/basic/part-01/exists-of-mem-vars-subst.md)
- [Subst congr](../../../unification/basic/part-01/subst-congr.md)
- [Vars](../../../unification/basic/part-01/vars.md)
- [Unifies](../../../unification/basic/part-01/unifies.md)
- [Unify](../../../unification/basic/part-02/unify.md)
- [Completeness](../../../unification/basic/part-02/unify-eq-none-iff.md)
- [Most generality](../../../unification/basic/part-02/unify-eq-some-comp.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Completeness](../../../../../../sources/v2/CSLibExt.md)
