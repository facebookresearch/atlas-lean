---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.dagShortestPaths
---

# Dag Shortest Paths

Validate topology with Kahn, then run the one-pass integer solver.
Failure preserves the sorter's processed and remaining lists; it does not return a cycle list.

## Depends on

- [Distances](../../bellman-ford/basic/distances.md)
- [Edge](../../bellman-ford/basic/edge.md)
- [Cost](cost.md)

## Proof depends on

- [Directed Adjacency](../../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Result](../../../topological-sort/result.md)
- [Sort](../../../topological-sort/sort.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Basic](../../../../../../../../sources/v2/CSLibExt.md)
