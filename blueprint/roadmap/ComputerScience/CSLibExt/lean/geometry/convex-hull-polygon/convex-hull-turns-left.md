---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.convexHull_turnsLeft
---

# Convex Hull turns Left

If the points are not all collinear, the hull polygon is strictly convex: written cyclically
as `H ++ H.take 2`, every consecutive triple turns strictly left, including at the two vertices
where the lower and upper chains meet.

## Depends on

- [Turns Left](turns-left.md)
- [Convex Hull](convex-hull.md)
- [Cross](../segment-intersection/cross.md)

## Proof depends on

- [Lower Hull](../convex-hull/lower-hull.md)
- [Lower Hull get Last?](../convex-hull/lower-hull-get-last.md)
- [Lower Hull head?](../convex-hull/lower-hull-head.md)
- [Lower Hull left of edges](../convex-hull/lower-hull-left-of-edges.md)
- [Lower Hull sublist](../convex-hull/lower-hull-sublist.md)
- [Lower Hull turn left](../convex-hull/lower-hull-turn-left.md)
- [Upper Hull](upper-hull.md)
- [Upper Hull get Last?](upper-hull-get-last.md)
- [Upper Hull head?](upper-hull-head.md)
- [Upper Hull left of edges](upper-hull-left-of-edges.md)
- [Upper Hull sublist](upper-hull-sublist.md)
- [Upper Hull turn left](upper-hull-turn-left.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ConvexHullPolygon](../../../../../../sources/v2/CSLibExt.md)
