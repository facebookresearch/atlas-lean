---
article_id: af_436fb216a3a5aeb8d9fdbc5c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.monge_three_circles
---

# Monge three circles

Monge's theorem (three circles): three circles in the plane with positive, pairwise
distinct radii and pairwise disjoint closed disks have collinear external homothety centers.
Circles are center-radius pairs, and each external homothety center is the explicit
externally-dividing ratio point on its center-line, well-defined by the distinct-radii
hypotheses.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Monge three circles general](monge-three-circles-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.MongeCircles](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Monge%27s_theorem (statement monge-s1). The source's hypothesis is that no circle lies inside another; the pairwise disjointness of the closed disks (`hd12`, `hd23`, `hd13`) is stronger. Omitted source case: the source also treats two circles of equal radius, whose external tangents are parallel and meet at a point at infinity. The distinct-radii hypotheses `h12`, `h23`, `h13` exclude it, and the affine formula for the centers cannot express it. It follows from `monge_three_circles_general`; the positivity hypotheses `hr₁`, `hr₂`, `hr₃` and the disjointness hypotheses are unused and keep the `Wanted` statement's shape. Proves `Wanted` entry `monge_three_circles`.
