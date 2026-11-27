# Regular splitting

Let $A$ be a real $n \times n$ matrix. A pair of real matrices $(M, N)$ with $A = M - N$ is a *regular splitting* of $A$ if $M$ is nonsingular and both $M^{-1}$ and $N$ have nonnegative entries. Its iteration is the [splitting iteration](../splitting-iteration.md) $x_{k+1} = M^{-1} N x_k + M^{-1} b$. For a [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md) with positive diagonal $D$, the [Jacobi splitting](../jacobi-and-gauss-seidel-iteration-matrices.md) $M = D$, $N = D - A$, is regular.

## Depends on

- [Splitting iteration](../splitting-iteration.md)
- [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md)
- [Jacobi and Gauss–Seidel iteration matrices](../jacobi-and-gauss-seidel-iteration-matrices.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.2, Definition 4.3 and the iteration (4.34). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
