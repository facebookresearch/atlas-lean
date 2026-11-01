---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.run_distance_minimal
---

# Run distance minimal

The computed estimate is no greater than the weight of any concrete input path.

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

- [Edge to Directed Adjacency iff](../../bellman-ford/basic/edge-to-directed-adjacency-iff.md)
- [Is Weighted Path append edge](../../bellman-ford/basic/is-weighted-path-append-edge.md)
- [Is Weighted Path tail](../../bellman-ford/basic/is-weighted-path-tail.md)
- [Is Weighted Path walk](../../bellman-ford/basic/is-weighted-path-walk.md)
- [Path Weight append edge](../../bellman-ford/basic/path-weight-append-edge.md)
- [Run source distance](run-source-distance.md)
- [Directed Adjacency](../../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Edge](../../../directed-adjacency-2/part-01/edge.md)
- [Walk](../../../directed-adjacency-2/part-01/walk.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Basic](../../../../../../../../sources/v2/CSLibExt.md)
