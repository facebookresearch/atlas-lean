---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.EdmondsKarp.shortestPath_sound
---

# Shortest Path sound

A returned shortest path is a nodup directed path with the BFS distance.

## Depends on

- [BFSResult](../../breadth-first-search-2/bfsresult.md)
- [Bfs](../../breadth-first-search-2/bfs.md)
- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Is Path](is-path.md)
- [Shortest Path](shortest-path.md)

## Proof depends on

- [Distance eq some iff shortest](../../breadth-first-search-2/distance-eq-some-iff-shortest.md)
- [Edge](../../directed-adjacency-2/part-01/edge.md)
- [Walk](../../directed-adjacency-2/part-01/walk.md)
- [Transpose](../../directed-adjacency-2/part-01/transpose.md)
- [Walk transpose iff](../../directed-adjacency-2/part-01/walk-transpose-iff.md)
- [Path From Distances](path-from-distances.md)
- [Path From Distances sound](path-from-distances-sound.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.EdmondsKarp](../../../../../../../sources/v2/CSLibExt.md)
