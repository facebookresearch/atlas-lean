# Symmetry criterion for matrices indexed by a product

Let $\rho$ and $\gamma$ be linearly ordered sets and let $A$ be a matrix with rows and columns indexed by $\rho \times \gamma$, with entries in any set. Then $A$ is symmetric if and only if three conditions hold: for each $a \in \rho$, the submatrix $(A_{(a, i), (a, j)})_{i, j}$ is symmetric; for each $i \in \gamma$, the submatrix $(A_{(a, i), (b, i)})_{a, b}$ is symmetric; and for all $a < b$ in $\rho$ and $i < j$ in $\gamma$, $A_{(a, i), (b, j)} = A_{(b, j), (a, i)}$ and $A_{(a, j), (b, i)} = A_{(b, i), (a, j)}$.

## Idea

A matrix indexed by pairs can be pictured on a grid, each index $(a, i)$ being a cell. Symmetry asks that the entry for every ordered pair of cells equal the entry for the reversed pair. The criterion sorts the pairs of cells by how they sit on the grid: in the same row, in the same column, or at opposite corners of a rectangle, and in the last case both diagonals of the rectangle must be checked. Each pair of distinct cells falls into exactly one case, which is why the three conditions together give symmetry. The criterion is used to verify symmetry of matrices built from grids, as in tensor-network evaluations.

## Statements

- [Symmetry criterion for matrices indexed by a product](is-symm-prod-iff.md)
