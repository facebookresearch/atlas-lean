---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.HasType.let_substTy
---

# Let subst Ty

The `let` rule after a substitution: if `e₁ : τ₁` in `Γ`, and `e₂` has type `τ₂` once `x`
is bound to the substituted generalization of `τ₁` in `s Γ`, then `let x = e₁ in e₂ : τ₂` in
`s Γ`.

## Depends on

- [Ctx](../typing/part-01/ctx.md)
- [Subst](../typing/part-01/subst.md)
- [Expr](../typing/part-01/expr.md)
- [Has Type](../typing/part-01/has-type.md)
- [Scheme](../typing/part-01/scheme.md)
- [Subst Ty](../typing/part-01/subst-ty.md)
- [Ty](../typing/part-01/ty.md)
- [Gen](../typing/part-01/gen.md)
- [Subst](../../../unification/basic/part-01/subst.md)

## Proof depends on

- [More General](../typing/part-01/more-general-2.md)
- [Cons](../typing/part-02/cons.md)
- [Of lookup eq](../typing/part-02/of-lookup-eq.md)
- [Ftv](../typing/part-01/ftv.md)
- [Lookup](../typing/part-01/lookup.md)
- [Lookup subst congr](../typing/part-01/lookup-subst-congr.md)
- [Generality](../typing/part-02/mono.md)
- [Substitution lemma](../typing/part-02/subst.md)
- [Above](../typing/part-02/above.md)
- [Gen subst more General](../typing/part-02/gen-subst-more-general.md)
- [Term](../../../unification/basic/part-01/term.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW](../../../../../../sources/v2/CSLibExt.md)
