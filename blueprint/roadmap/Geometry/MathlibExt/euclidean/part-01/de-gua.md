---
article_id: af_64ac6a86e285db8a98f65d03
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.deGua
---

# De Gua

De Gua's theorem (statement `degua-s1`): a trirectangular tetrahedron with legs `u`,
  `v`, `w` (mutually orthogonal edges from one vertex, via inner-product zeros) satisfies
  Area(hypotenuse face)^2 = Area1^2 + Area2^2 + Area3^2. The right-face areas are
  half-products of leg norms; the hypotenuse-face area is the genuine 2D triangular area
  via the Gram determinant (Lagrange identity for half the cross-product norm), not a
  vacuous 3D volume. Source: https://en.wikipedia.org/wiki/De_Gua%27s_theorem
Proves `Wanted` entry `deGua`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.DeGua](../../../../../sources/v2/MathlibExt.md)
