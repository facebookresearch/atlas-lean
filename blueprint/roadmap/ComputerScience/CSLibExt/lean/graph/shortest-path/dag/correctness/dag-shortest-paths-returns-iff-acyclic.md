---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.dagShortestPaths_returns_iff_acyclic
---

# Dag Shortest Paths returns iff acyclic

The total wrapper succeeds exactly on DAGs, including disconnected DAGs.

## Depends on

- [Distances](../../bellman-ford/basic/distances.md)
- [Edge](../../bellman-ford/basic/edge.md)
- [To Directed Adjacency](../../bellman-ford/basic/to-directed-adjacency.md)
- [Cost](../basic/cost.md)
- [Dag Shortest Paths](../basic/dag-shortest-paths.md)
- [Is Acyclic](../../../topological-sort/is-acyclic.md)

## Proof depends on

- [Dag Shortest Paths eq ok iff](../basic/dag-shortest-paths-eq-ok-iff.md)
- [Run](../basic/run.md)
- [Is Topological Order](../../../topological-sort/is-topological-order.md)
- [Result](../../../topological-sort/result.md)
- [Sort](../../../topological-sort/sort.md)
- [Succeeds iff acyclic](../../../topological-sort/succeeds-iff-acyclic.md)
- [Success is Topological Order](../../../topological-sort/success-is-topological-order.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
