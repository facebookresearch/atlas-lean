---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BellmanFord.bellmanFord_total_le
---

# Bellman Ford total le

The abstract event count is bounded by `4 * |V| * |E|`.

## Depends on

- [Cost](../basic/cost.md)
- [Total](../basic/total.md)
- [Edge](../basic/edge.md)
- [Result](../basic/result.md)
- [Bellman Ford](../correctness/bellman-ford.md)

## Proof depends on

- [Distances](../basic/distances.md)
- [Is Weighted Path](../basic/is-weighted-path.md)
- [Reachable Negative Cycle](../basic/reachable-negative-cycle.md)
- [Bellman Ford cycle Witness Steps le](bellman-ford-cycle-witness-steps-le.md)
- [Bellman Ford relaxation Checks eq mul](bellman-ford-relaxation-checks-eq-mul.md)
- [Path Vertices](../basic/path-vertices.md)
- [Path Weight](../basic/path-weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Costs](../../../../../../../../sources/v2/CSLibExt.md)
