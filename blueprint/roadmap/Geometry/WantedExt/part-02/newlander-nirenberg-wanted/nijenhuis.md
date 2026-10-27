---
article_id: af_bcdcdd3b700c0bf06475c11a
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Geometry.NewlanderNirenbergWanted.Geometry.NewlanderNirenberg.nijenhuis
---

# Nijenhuis

The **Nijenhuis tensor** of a field of endomorphisms `J` on `ℝ^{2n}`,
evaluated on two vector fields `V`, `W` at a point:

`N(V, W) = [JV, JW] - J[JV, W] - J[V, JW] - [V, W]`.

For an almost complex structure the last term is `J²[V, W]`, so this is the
usual torsion of `J`. When `U` is open and `IsAlmostComplexOn J U` holds, the
expression is `C^∞(U)`-bilinear in `V` and `W` on `U`: the terms involving the
derivatives of `V` and `W` cancel using `J² = -1`, so the value at a point of
`U` depends only on `V x`, `W x` and the derivative of `J` there.

## Depends on

- [E](e.md)

## Sources

- [WantedExt, WantedExt.Geometry.NewlanderNirenbergWanted](../../../../../sources/v2/WantedExt.md)
