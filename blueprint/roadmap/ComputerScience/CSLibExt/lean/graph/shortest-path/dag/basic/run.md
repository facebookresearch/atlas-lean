---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DAGShortestPaths.run
---

# Run

Execute one outgoing-edge relaxation pass in a certified topological order.
The original edge occurrences are retained, so every parallel occurrence is checked.

## Depends on

- [Distances](../../bellman-ford/basic/distances.md)
- [Edge](../../bellman-ford/basic/edge.md)
- [To Directed Adjacency](../../bellman-ford/basic/to-directed-adjacency.md)
- [Cost](cost.md)
- [Is Topological Order](../../../topological-sort/is-topological-order.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Basic](../../../../../../../../sources/v2/CSLibExt.md)
