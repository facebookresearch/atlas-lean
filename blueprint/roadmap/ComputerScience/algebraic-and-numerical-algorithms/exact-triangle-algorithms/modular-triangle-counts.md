# Modular triangle counts and false positives

For an Exact Triangle instance $(A, B, C)$ and a prime $p$, let $Z_p$ be the number of triangles $(i, j, k)$ with $A_{ij} + B_{jk} + C_{ik} \equiv 0 \pmod p$, let $Z$ be the number of zero triangles, and let the **false positive count** be $F_p = Z_p - Z$, the number of triangles whose weight is nonzero but divisible by $p$.

## Depends on

- [Exact Triangle](exact-triangle-problem.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
