---
declaration: def
origin: cited
statement: formalized
lean: Cslib.HindleyMilner.W
---

# W

Algorithm W. `W Γ e n` returns a substitution `s`, a type `τ`, and the next fresh
variable, or `none` when unification fails or a variable is unbound. Type variables
`var m` with `m ≥ n` are used as fresh.

## Depends on

- [Ctx](../typing/part-01/ctx.md)
- [Expr](../typing/part-01/expr.md)
- [Ty](../typing/part-01/ty.md)
- [Subst](../../../unification/basic/part-01/subst.md)

## Proof depends on

- [Lookup](../typing/part-01/lookup.md)
- [Subst](../typing/part-01/subst.md)
- [Scheme](../typing/part-01/scheme.md)
- [Bound Sup](bound-sup.md)
- [Inst](../typing/part-01/inst.md)
- [Gen](../typing/part-01/gen.md)
- [To Scheme](../typing/part-01/to-scheme.md)
- [Comp](../../../unification/basic/part-01/comp.md)
- [Term](../../../unification/basic/part-01/term.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)
- [Unify](../../../unification/basic/part-02/unify.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW](../../../../../../sources/v2/CSLibExt.md)
