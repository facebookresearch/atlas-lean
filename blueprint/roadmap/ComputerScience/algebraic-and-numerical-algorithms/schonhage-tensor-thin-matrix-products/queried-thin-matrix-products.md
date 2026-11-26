# Queried thin matrix products in sub-output time

There is a deterministic word-RAM program that, given an $N \times D$ matrix $A$ and a $D \times N$ matrix $B$ of signed integers with entries bounded by $M$, and $Q$ query positions $(i_q, j_q)$, returns $(AB)_{i_q j_q}$ for all $q$. When $D = 4^m$, $D^{18} \le N$ and $Q \cdot 2^m \le N^2$, it uses at most

$$
c\,(19m + 1)\, \frac{N^2}{D^{1/18}}
$$

instructions for an absolute constant $c$, at every word size $w \ge 128 \lceil \log_2(N + Q + M + 2) \rceil$. Without the occurrence bound, distinct-set sparsity still gives the saving plus an additive charge per query occurrence.

## Proof sketch

The program computes valid level-set tables, shared band encodings, tile keys and query codes, groups queries by tile with a stable counting scatter, and runs pruned traversals per tile; the sparse leaf bound charges the traversals.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Schönhage's ten-term tensor](schonhage-ten-term-tensor.md)

## Proof depends on

- [Exact queried entries of thin products via tiling](thin-product-correctness.md)
- [Sparse query bound for contributing leaves](sparse-leaf-bound.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
