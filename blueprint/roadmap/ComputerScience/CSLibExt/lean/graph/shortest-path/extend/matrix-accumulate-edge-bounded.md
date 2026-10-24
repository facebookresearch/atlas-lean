---
article_id: af_fd3bc332c73538c0a1842737
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Matrix.matrixAccumulate_edgeBounded
---

# Matrix Accumulate edge Bounded

With a zero diagonal and a previous at-most-`r`-edge distance matrix,
the actual infinity-initialized min-plus run returns at-most-`r+1`-edge
shortest weights. This includes repeated walks and signed edge weights.

## Depends on

- [Is Edge Bounded Shortest Path Weight](is-edge-bounded-shortest-path-weight.md)
- [Matrix Accumulate](../../../matrix/multiply/matrix-accumulate.md)

## Proof depends on

- [Is Weighted Path](../floyd-warshall/basic/is-weighted-path.md)
- [Path Weight](../floyd-warshall/basic/path-weight.md)
- [Matrix Accumulate min Plus apply](matrix-accumulate-min-plus-apply.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend](../../../../../../../sources/v2/CSLibExt.md)
