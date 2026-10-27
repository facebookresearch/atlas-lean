---
article_id: af_19cbe89ae89f02d2c956b618
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.descartes_circle_theorem
---

# Descartes Circle Theorem

Descartes' circle theorem (statement_id `descartes-kissing-s1`): four pairwise
tangent circles in the plane, with tangency distance-encoded and with signed
curvatures `k i` (curvature `1 / r i`, negative for the enclosing circle),
satisfy `(∑ k) ^ 2 = 2 * ∑ k ^ 2`.

Proof: Following the Cayley-Menger/Gram-determinant argument in Lagarias, Mallows, and Wilks,
*Beyond the Descartes circle theorem*, Section 3, and Wikipedia's proof sketch, introduce signed
radii, expand the planar Gram determinant in coordinates, and clear denominators.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.DescartesCircleTheorem](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Descartes%27_theorem.
