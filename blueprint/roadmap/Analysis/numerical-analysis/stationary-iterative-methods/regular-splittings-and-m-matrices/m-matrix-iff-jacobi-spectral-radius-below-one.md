# Nonsingular M-matrices are characterized by their Jacobi iteration matrices

Let $A$ be a real $n \times n$ [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md) with $a_{ii} > 0$ for all $i$, and let $D$ be its diagonal. Then $A$ is a [nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md) if and only if its [Jacobi iteration matrix](../jacobi-and-gauss-seidel-iteration-matrices.md) satisfies

$$\rho(I - D^{-1}A) < 1,$$

that is, exactly when the Jacobi iteration for $Ax = b$ converges for every right-hand side $b$ and every starting vector.

## Depends on

- [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md)
- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)
- [Jacobi and Gauss–Seidel iteration matrices](../jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [A nonnegative inverse of I − B forces ρ(B) < 1](nonnegative-inverse-forces-spectral-radius-below-one.md)
- [A Z-matrix is a nonsingular M-matrix if and only if its inverse is nonnegative](z-matrix-is-a-nonsingular-m-matrix-iff-its-inverse-is-nonnegative.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, the argument after Definition 1.30 and Theorem 1.31 with its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
