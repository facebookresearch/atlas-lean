---
article_id: af_c61b92515e99f372d836bba2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.FloydWarshall.floydWarshall_hasNegativeDiagonal_sound
---

# Floyd Warshall has Negative Diagonal sound

A negative diagonal entry in the computed matrix implies a simple negative cycle.

## Depends on

- [Cost](../basic/cost.md)
- [Has Negative Cycle](../basic/has-negative-cycle.md)
- [Floyd Warshall](../basic/floyd-warshall.md)
- [Has Negative Diagonal](../basic/has-negative-diagonal.md)

## Proof depends on

- [Is Negative Cycle](../basic/is-negative-cycle.md)
- [Is Weighted Path](../basic/is-weighted-path.md)
- [Floyd Warshall distance realized](floyd-warshall-distance-realized.md)
- [Has Negative Diagonal eq true iff](../basic/has-negative-diagonal-eq-true-iff.md)
- [Path Weight](../basic/path-weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
