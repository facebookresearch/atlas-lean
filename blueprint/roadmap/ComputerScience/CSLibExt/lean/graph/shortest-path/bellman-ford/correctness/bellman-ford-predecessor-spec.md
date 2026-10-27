---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BellmanFord.bellmanFord_predecessor_spec
---

# Bellman Ford predecessor spec

Every returned predecessor is a tight input edge for the final distances.

## Depends on

- [Cost](../basic/cost.md)
- [Distances](../basic/distances.md)
- [Edge](../basic/edge.md)
- [Result](../basic/result.md)
- [Bellman Ford](bellman-ford.md)

## Proof depends on

- [Is Weighted Path](../basic/is-weighted-path.md)
- [Reachable Negative Cycle](../basic/reachable-negative-cycle.md)
- [Path Vertices](../basic/path-vertices.md)
- [Path Weight](../basic/path-weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
