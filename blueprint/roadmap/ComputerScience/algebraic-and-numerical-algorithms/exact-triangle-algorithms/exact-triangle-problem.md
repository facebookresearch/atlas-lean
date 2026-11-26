# Exact Triangle

**Exact Triangle.** Given three $t \times t$ integer matrices $A$, $B$, $C$, viewed as edge weights between the first and second, the second and third, and the first and third parts of a complete tripartite graph with $t$ vertices per part, decide whether there are $i, j, k \in \{1, \dots, t\}$ with

$$
A_{ij} + B_{jk} + C_{ik} = 0 .
$$

Such $(i, j, k)$ is a **zero triangle**. Weights are polynomially bounded with exponent $\kappa$ if every entry has absolute value at most $(t+2)^\kappa$.

## Depends on

- [Negative triangles in tripartite weighted graphs](../../graph-algorithms/shortest-paths/negative-triangle-reductions/negative-triangle.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Finding, Minimizing, and Counting Weighted Subgraphs", SIAM Journal on Computing 42(3), 2013.
- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
