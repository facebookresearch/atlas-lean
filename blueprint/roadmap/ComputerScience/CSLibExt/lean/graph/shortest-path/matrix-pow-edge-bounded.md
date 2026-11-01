---
article_id: af_34ebf61dbc02f1af60d9a016
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Matrix.matrix_pow_edgeBounded
---

# Matrix Power

A min-plus matrix power gives optimal weights among walks with at most
`r` edges when the source diagonal is zero. Repeated vertices are allowed.

## Depends on

- [Is Edge Bounded Shortest Path Weight](extend/is-edge-bounded-shortest-path-weight.md)

## Proof depends on

- [Is Weighted Path](floyd-warshall/basic/is-weighted-path.md)
- [Path Weight](floyd-warshall/basic/path-weight.md)
- [Matrix Accumulate](../../matrix/multiply/matrix-accumulate.md)
- [Matrix Accumulate edge Bounded](extend/matrix-accumulate-edge-bounded.md)
- [Matrix Accumulate ret](../../matrix/multiply/matrix-accumulate-ret.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.MatrixPower](../../../../../../sources/v2/CSLibExt.md)
