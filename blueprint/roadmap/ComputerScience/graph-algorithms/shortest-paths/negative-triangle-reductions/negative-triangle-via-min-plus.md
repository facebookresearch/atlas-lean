# Negative triangle detection with one (min,+) product

A tripartite graph $(A, B, C)$ has a negative triangle if and only if $\min_{i,j}\big((A \star B)_{ij} + C_{ij}\big) < 0$. Hence negative triangle detection reduces to one $(\min,+)$ product plus $O(n^2)$ additional comparisons.

## Depends on

- [Negative triangles in tripartite weighted graphs](negative-triangle.md)
- [Min-plus matrix powers give shortest path weights with at most $r$ edges](../all-pairs-shortest-paths-by-min-plus-products/matrix-pow-edge-bounded.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
