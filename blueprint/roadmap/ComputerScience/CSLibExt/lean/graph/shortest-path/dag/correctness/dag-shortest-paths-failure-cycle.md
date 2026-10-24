---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.dagShortestPaths_failure_cycle
---

# Dag Shortest Paths failure cycle

Every failure certifies an actual directed cycle among the remaining vertices.

## Depends on

- [Distances](../../bellman-ford/basic/distances.md)
- [Edge](../../bellman-ford/basic/edge.md)
- [To Directed Adjacency](../../bellman-ford/basic/to-directed-adjacency.md)
- [Cost](../basic/cost.md)
- [Dag Shortest Paths](../basic/dag-shortest-paths.md)
- [Directed Cycle In](../../../topological-sort/directed-cycle-in.md)

## Proof depends on

- [Dag Shortest Paths eq error iff](../basic/dag-shortest-paths-eq-error-iff.md)
- [Result](../../../topological-sort/result.md)
- [Failure cycle](../../../topological-sort/failure-cycle.md)
- [Sort](../../../topological-sort/sort.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
