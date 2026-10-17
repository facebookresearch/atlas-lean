---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.infer_principal
---

# Principal types

**Principal types**: the inferred type of a closed expression is one of its types, and
every type of it is an instance of the inferred one.

## Depends on

- [Expr](../typing/part-01/expr.md)
- [Has Type](../typing/part-01/has-type.md)
- [Scheme](../typing/part-01/scheme.md)
- [Ty](../typing/part-01/ty.md)
- [Infer](../algorithm-w/infer.md)
- [Subst](../../../unification/basic/part-01/subst.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)

## Proof depends on

- [Has Type of infer eq some](../algorithm-w/has-type-of-infer-eq-some.md)
- [Infer complete](infer-complete.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Completeness](../../../../../../sources/v2/CSLibExt.md)
