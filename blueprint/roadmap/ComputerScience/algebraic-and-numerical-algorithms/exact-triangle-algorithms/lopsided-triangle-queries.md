# Lopsided triangle queries

A **lopsided triangle query** consists of two outer parts $U, V$ of $n$ vertices each, a middle part identified with a subset of $\{1, \dots, D\}$ with $D \ll n$, $0/1$ adjacency matrices $X \in \{0,1\}^{U \times [D]}$ and $Y \in \{0,1\}^{[D] \times V}$, and a set $W \subseteq U \times V$ of queried outer pairs. The answer is the common-neighbour count $(XY)_{uv}$ for each $(u, v) \in W$; when $W$ is the set of outer edges, a positive answer at $(u,v)$ says that the edge $uv$ lies on a triangle.

## Depends on

- [Exact Triangle](exact-triangle-problem.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
