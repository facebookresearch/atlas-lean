---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.run_distance_realized
---

# Run distance realized

Each finite estimate returned by the executed one-pass solver is realized by an input path.

## Depends on

- [Distances](../../bellman-ford/basic/distances.md)
- [Edge](../../bellman-ford/basic/edge.md)
- [Is Weighted Path](../../bellman-ford/basic/is-weighted-path.md)
- [Path Weight](../../bellman-ford/basic/path-weight.md)
- [To Directed Adjacency](../../bellman-ford/basic/to-directed-adjacency.md)
- [Cost](cost.md)
- [Run](run.md)
- [Is Topological Order](../../../topological-sort/is-topological-order.md)

## Proof depends on

- [Is Weighted Path append edge](../../bellman-ford/basic/is-weighted-path-append-edge.md)
- [Path Weight append edge](../../bellman-ford/basic/path-weight-append-edge.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Basic](../../../../../../../../sources/v2/CSLibExt.md)
