---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.convexHull_left_of_edges
---

# Convex Hull left of edges

For at least two points, every input point is on or left of every edge of the closed hull
polygon `H ++ [H.head]`: the polygon contains all the points.

## Depends on

- [Convex Hull](convex-hull.md)
- [Cross](../segment-intersection/cross.md)

## Proof depends on

- [Lower Hull](../convex-hull/lower-hull.md)
- [Lower Hull get Last?](../convex-hull/lower-hull-get-last.md)
- [Lower Hull head?](../convex-hull/lower-hull-head.md)
- [Lower Hull left of edges](../convex-hull/lower-hull-left-of-edges.md)
- [Upper Hull](upper-hull.md)
- [Upper Hull get Last?](upper-hull-get-last.md)
- [Upper Hull head?](upper-hull-head.md)
- [Upper Hull left of edges](upper-hull-left-of-edges.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ConvexHullPolygon](../../../../../../sources/v2/CSLibExt.md)
