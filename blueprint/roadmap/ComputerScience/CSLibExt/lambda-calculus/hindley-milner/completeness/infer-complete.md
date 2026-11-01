---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.infer_complete
---

# Infer complete

`infer` succeeds on every typable closed expression, with a type of which every other type
is an instance.

## Depends on

- [Expr](../typing/part-01/expr.md)
- [Has Type](../typing/part-01/has-type.md)
- [Scheme](../typing/part-01/scheme.md)
- [Ty](../typing/part-01/ty.md)
- [Infer](../algorithm-w/infer.md)
- [Subst](../../../unification/basic/part-01/subst.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)

## Proof depends on

- [Ctx](../typing/part-01/ctx.md)
- [Ftv](../typing/part-01/ftv.md)
- [Subst](../typing/part-01/subst.md)
- [Visible Vars](../typing/part-01/visible-vars.md)
- [Subst Ty](../typing/part-01/subst-ty.md)
- [W](../algorithm-w/w.md)
- [Completeness of Algorithm W](w-complete.md)
- [Term](../../../unification/basic/part-01/term.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Completeness](../../../../../../sources/v2/CSLibExt.md)
