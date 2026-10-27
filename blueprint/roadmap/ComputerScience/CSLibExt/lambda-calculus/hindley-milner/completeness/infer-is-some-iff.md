---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.infer_isSome_iff
---

# Infer is Some iff

`infer` succeeds exactly on the typable closed expressions.

## Depends on

- [Expr](../typing/part-01/expr.md)
- [Has Type](../typing/part-01/has-type.md)
- [Scheme](../typing/part-01/scheme.md)
- [Ty](../typing/part-01/ty.md)
- [Infer](../algorithm-w/infer.md)

## Proof depends on

- [Has Type of infer eq some](../algorithm-w/has-type-of-infer-eq-some.md)
- [Infer complete](infer-complete.md)
- [Subst](../../../unification/basic/part-01/subst.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Completeness](../../../../../../sources/v2/CSLibExt.md)
