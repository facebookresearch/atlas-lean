# Inverse-nonnegative Z-matrices have positive diagonal

Let $A$ be a real $n \times n$ [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md), $a_{ij} \le 0$ for $i \ne j$, nonsingular, with $A^{-1} \ge 0$ entrywise. Then $a_{ii} > 0$ for every $i$, since $1 = (AA^{-1})_{ii} = a_{ii}(A^{-1})_{ii} + \sum_{j \ne i} a_{ij}(A^{-1})_{ji} \le a_{ii}(A^{-1})_{ii}$, and the [Jacobi iteration matrix](../jacobi-and-gauss-seidel-iteration-matrices.md) satisfies $\rho(I - D^{-1}A) < 1$ for the diagonal $D$ of $A$, since the Jacobi splitting is then regular.

## Depends on

- [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md)
- [Jacobi and Gauss–Seidel iteration matrices](../jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [Convergence of regular splittings](regular-splitting-convergence.md)
- [Regular splitting](regular-splitting.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, Theorem 1.32 and its proof from $(AA^{-1})_{ii} = 1$. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
