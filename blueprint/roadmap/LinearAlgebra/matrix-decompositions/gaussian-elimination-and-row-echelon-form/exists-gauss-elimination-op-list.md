# Gaussian elimination as a product of row operations

Let $K$ be a field and let $A$ be a
matrix over $K$ whose rows and columns are indexed by finite linearly ordered sets. Then there
are a permutation $\sigma$ of the row indices and a finite, possibly empty, list
$M_1, \dots, M_\ell$ of square matrices over $K$ indexed by the row indices, each lower
triangular with every diagonal entry equal to $1$, such that the matrix
$M_1 M_2 \cdots M_\ell A_\sigma$ is in row echelon form. Here $A_\sigma$ is the matrix with
entries $(A_\sigma)_{ic} = A_{\sigma(i) c}$, the empty product is the identity matrix, and a
matrix $B$ is in row echelon form when for all rows $i_1 < i_2$ and every column $c$, if
$B_{i_1 c'} = 0$ for every column $c' < c$, then $B_{i_2 c} = 0$.

This records the factorization, not the intermediate matrices of an algorithm trace.

Proof: Induct on the columns after identifying the ordered index sets with initial segments of
the natural numbers; a nonzero first column uses a row pivot and recurses on the lower-right
block. Package the resulting single unit lower-triangular matrix as a one-element list (forward
elimination to row echelon form, https://en.wikipedia.org/wiki/Gaussian_elimination).

## Sources

- L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lectures 20-21.
