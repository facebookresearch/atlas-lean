# For two-cyclic matrices Gauss–Seidel converges twice as fast as Jacobi

Let $A = \begin{pmatrix} D_1 & A_{12} \\ A_{21} & D_2 \end{pmatrix}$ be an $n \times n$ matrix whose diagonal blocks $D_1$ and $D_2$ are nonsingular diagonal matrices, as for a matrix with Property A whose unknowns of the first colour are numbered before those of the second. Then the spectral radii of its [Gauss–Seidel and Jacobi iteration matrices](jacobi-and-gauss-seidel-iteration-matrices.md) satisfy

$$\rho(G_{GS}) = \rho(G_J)^2.$$

So when $\rho(G_J) < 1$, one Gauss–Seidel sweep reduces the error asymptotically as much as two Jacobi sweeps.

## Depends on

- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [Consistently ordered matrix](consistently-ordered-matrix.md)
- [Young's relation between SOR and Jacobi eigenvalues](young-sor-jacobi-eigenvalue-relation.md)

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), Theorem 4 and its proof (the case $w = 1$ of the relation $(\lambda + w - 1)^2 = \lambda w^2 \mu^2$), referring to J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997, Theorem 6.6. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
