---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Geometry.direction
---

# Direction

CLRS `DIRECTION(pᵢ, pⱼ, pₖ) = (pₖ - pᵢ) × (pⱼ - pᵢ)`: positive when `pₖ` is clockwise from
`pⱼ` about `pᵢ`, negative when counterclockwise, zero when the three points are collinear.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cross](cross.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection](../../../../../../sources/v2/CSLibExt.md)
