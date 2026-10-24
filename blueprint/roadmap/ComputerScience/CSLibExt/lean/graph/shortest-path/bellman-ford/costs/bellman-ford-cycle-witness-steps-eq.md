---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BellmanFord.bellmanFord_cycleWitnessSteps_eq
---

# Bellman Ford cycle Witness Steps eq

A returned cycle is charged one step per localization, cycle, and prefix edge.

## Depends on

- [Cost](../basic/cost.md)
- [Edge](../basic/edge.md)
- [Reachable Negative Cycle](../basic/reachable-negative-cycle.md)
- [Result](../basic/result.md)
- [Bellman Ford](../correctness/bellman-ford.md)

## Proof depends on

- [Distances](../basic/distances.md)
- [Is Weighted Path](../basic/is-weighted-path.md)
- [Path Vertices](../basic/path-vertices.md)
- [Path Weight](../basic/path-weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Costs](../../../../../../../../sources/v2/CSLibExt.md)
