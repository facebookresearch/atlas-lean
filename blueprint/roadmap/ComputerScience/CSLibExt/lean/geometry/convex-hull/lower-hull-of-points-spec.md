---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.lowerHullOfPoints_spec
---

# Lower Hull Of Points spec

For distinct points in any order: the chain's vertices are input points, it starts at the
least and ends at the greatest point in `(x, y)` order, turns strictly left, and has every point
on or left of each edge.

## Depends on

- [Cross](../segment-intersection/cross.md)
- [Lower Hull Of Points](lower-hull-of-points.md)

## Proof depends on

- [Lower Hull](lower-hull.md)
- [Lower Hull get Last?](lower-hull-get-last.md)
- [Lower Hull head?](lower-hull-head.md)
- [Lower Hull left of edges](lower-hull-left-of-edges.md)
- [Lower Hull sublist](lower-hull-sublist.md)
- [Lower Hull turn left](lower-hull-turn-left.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ConvexHull](../../../../../../sources/v2/CSLibExt.md)
