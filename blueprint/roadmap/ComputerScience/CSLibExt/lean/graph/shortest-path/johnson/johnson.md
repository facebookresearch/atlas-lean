---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Johnson.johnson
---

# Basic

Johnson's integer all-pairs distances, with signed decoding and a complete dense table.
`none` reports a negative cycle anywhere in the original graph. The cost counts the selected
construction, scan, relaxation and decoding actions, not full RAM or bit complexity.

## Depends on

- [Edge](../bellman-ford/basic/edge.md)

## Proof depends on

- [Cost](../bellman-ford/basic/cost.md)
- [Total](../bellman-ford/basic/total.md)
- [Distances](../bellman-ford/basic/distances.md)
- [Reachable Negative Cycle](../bellman-ford/basic/reachable-negative-cycle.md)
- [Result](../bellman-ford/basic/result.md)
- [Bellman Ford](../bellman-ford/correctness/bellman-ford.md)
- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Dijkstra Cost](../dijkstra/dijkstra-cost.md)
- [Total](../dijkstra/total.md)
- [Dijkstra Result](../dijkstra/dijkstra-result.md)
- [Dijkstra](../dijkstra/dijkstra.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic](../../../../../../../sources/v2/CSLibExt.md)
