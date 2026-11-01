---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Geometry.popNonLeft
---

# Pop Non Left

Pop the top of the stack (top first) while it does not make a strict left turn towards `p`:
the stack `a :: b :: rest` loses `a` when `cross (a - b) (p - b) ≤ 0`. One unit per test.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cross](../segment-intersection/cross.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ConvexHull](../../../../../../sources/v2/CSLibExt.md)
