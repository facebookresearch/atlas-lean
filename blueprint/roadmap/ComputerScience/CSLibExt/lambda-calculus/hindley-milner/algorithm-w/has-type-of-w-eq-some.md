---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.hasType_of_W_eq_some
---

# Soundness of Algorithm W

**Soundness of Algorithm W**: a returned substitution `s` and type `τ` satisfy
`s Γ ⊢ e : τ`.

## Depends on

- [Ctx](../typing/part-01/ctx.md)
- [Subst](../typing/part-01/subst.md)
- [Expr](../typing/part-01/expr.md)
- [Has Type](../typing/part-01/has-type.md)
- [Ty](../typing/part-01/ty.md)
- [W](w.md)
- [Subst](../../../unification/basic/part-01/subst.md)

## Proof depends on

- [Lookup](../typing/part-01/lookup.md)
- [Let subst Ty](let-subst-ty.md)
- [Substitution lemma](../typing/part-02/subst.md)
- [Scheme](../typing/part-01/scheme.md)
- [Bound Sup](bound-sup.md)
- [Inst](../typing/part-01/inst.md)
- [Subst Ty](../typing/part-01/subst-ty.md)
- [Gen](../typing/part-01/gen.md)
- [To Scheme](../typing/part-01/to-scheme.md)
- [Equations](../../../unification/basic/part-01/equations.md)
- [Comp](../../../unification/basic/part-01/comp.md)
- [Term](../../../unification/basic/part-01/term.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)
- [Unifies](../../../unification/basic/part-01/unifies.md)
- [Soundness](../../../unification/basic/part-02/unifies-unify.md)
- [Unify](../../../unification/basic/part-02/unify.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW](../../../../../../sources/v2/CSLibExt.md)
