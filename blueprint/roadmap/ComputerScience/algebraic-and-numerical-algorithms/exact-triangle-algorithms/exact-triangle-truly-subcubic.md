# Exact Triangle in truly subcubic word-RAM time

For every fixed $\kappa \ge 1$ there is a single deterministic word-RAM program that decides Exact Triangle on $n$-vertex-per-part instances with weights bounded by $n^\kappa$ in time

$$
O_\kappa\!\left(n^{3 - 33/20000}\right),
$$

at every word size $w \ge c_\kappa \log_2 (n + 2)$, returning a zero triangle when one exists. The program computes its own block parameters and selects a minimum-count prime itself; the constants and thresholds depend only on $\kappa$.

## Proof sketch

Choose $D$ with $D^{18} \le n$ and a group count $g$ so that preparation, query control and products all cost $O(n^3/g)$. Count modular zero triangles with the cyclic Strassen recursion to select a prime, answer the lopsided queries by Schönhage-based thin matrix products with routed boxes, and recover a witness by scanning; the false-positive bound keeps scanning within budget.

## Depends on

- [Exact Triangle](exact-triangle-problem.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Proof depends on

- [A minimum-count prime has few false positives](minimum-count-prime-selection.md)
- [Counting modular zero triangles by matrix multiplication over a cyclic ring](modular-triangle-count-by-cyclic-matrix-product.md)
- [Splitting Exact Triangle into lopsided triangle queries](exact-triangle-modular-splitting.md)
- [Witness recovery from modular lopsided answers](exact-triangle-witness-recovery.md)
- [Routed box products with one shared box geometry](../schonhage-tensor-thin-matrix-products/routed-box-products.md)
- [Queried thin matrix products in sub-output time](../schonhage-tensor-thin-matrix-products/queried-thin-matrix-products.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
