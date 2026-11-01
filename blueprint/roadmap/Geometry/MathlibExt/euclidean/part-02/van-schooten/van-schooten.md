---
article_id: af_6c7dc4108508284fd5edbe59
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.vanSchooten
---

# Van Schooten

Van Schooten's theorem: an equilateral triangle `ABC` with a point `P` on the
circumcircle on arc `AB` not containing `C` satisfies `PA + PB = PC`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Van Schooten general](van-schooten-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.VanSchooten](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Van_Schooten%27s_theorem. It follows from `vanSchooten_general`; the hypotheses `P ≠ A`, `P ≠ B` and `P ≠ C` are unused and keep the source's shape. Proves `Wanted` entry `vanSchooten`.
