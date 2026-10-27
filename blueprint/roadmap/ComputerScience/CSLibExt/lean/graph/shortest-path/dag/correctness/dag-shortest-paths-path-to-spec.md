---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.dagShortestPaths_pathTo?_spec
---

# Dag Shortest Paths path To? spec

A successful-wrapper predecessor path is an actual shortest path with at most n-1 edges.

## Depends on

- [Distances](../../bellman-ford/basic/distances.md)
- [Path To?](../../bellman-ford/basic/path-to.md)
- [Edge](../../bellman-ford/basic/edge.md)
- [Is Weighted Path](../../bellman-ford/basic/is-weighted-path.md)
- [Path Weight](../../bellman-ford/basic/path-weight.md)
- [Cost](../basic/cost.md)
- [Dag Shortest Paths](../basic/dag-shortest-paths.md)

## Proof depends on

- [To Directed Adjacency](../../bellman-ford/basic/to-directed-adjacency.md)
- [Dag Shortest Paths eq ok iff](../basic/dag-shortest-paths-eq-ok-iff.md)
- [Run](../basic/run.md)
- [Run path To? spec](run-path-to-spec.md)
- [Is Topological Order](../../../topological-sort/is-topological-order.md)
- [Result](../../../topological-sort/result.md)
- [Sort](../../../topological-sort/sort.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
