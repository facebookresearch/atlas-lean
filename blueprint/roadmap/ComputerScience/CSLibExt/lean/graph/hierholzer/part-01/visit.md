---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.visit
---

# Visit

Hierholzer's recursion with fuel. `visit fuel v R acc` follows unused edges from `v` depth
first, splicing sub-tours in, and returns the emitted vertices prepended to `acc` together with
the remaining adjacency `R`. Fuel `0` returns `(acc, R)` unchanged and too little fuel can stop
early; with more fuel than remaining edges and a remainder unbalanced only by `v → … → t`, the
contract is `visit_spec`. `hierholzer` passes one more than the number of edges.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Hierholzer](../../../../../../../sources/v2/CSLibExt.md)
