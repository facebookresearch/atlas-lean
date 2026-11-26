# For two-cyclic matrices the Gauss–Seidel spectral radius is the square of the Jacobi one

Let $A = \begin{pmatrix} D_1 & A_{12} \\ A_{21} & D_2 \end{pmatrix}$ be an $n \times n$ matrix whose diagonal blocks $D_1$ and $D_2$ are nonsingular diagonal matrices, as for a matrix with Property A whose unknowns of the first colour are numbered before those of the second. Then the spectral radii of its [Gauss–Seidel and Jacobi iteration matrices](jacobi-and-gauss-seidel-iteration-matrices.md) satisfy

$$\rho(G_{GS}) = \rho(G_J)^2.$$

So when $0 < \rho(G_J) < 1$, both iterations converge and the asymptotic convergence rate of Gauss–Seidel, $-\log \rho(G_{GS})$, is twice that of Jacobi. This compares worst-case rates over all starting vectors; for a particular starting vector the errors can behave otherwise: for $A = \begin{pmatrix} 2 & -1 \\ -1 & 2 \end{pmatrix}$, $b = 0$ and $x_0 = (1, 0)$, one Gauss–Seidel sweep gives $0$, while two Jacobi sweeps give $(1/4, 0)$. When $\rho(G_J) = 0$, both iteration matrices are nilpotent and both iterations reach the solution after at most $n$ steps, for example after one step for $A = I$. When $\rho(G_J) \ge 1$, neither method guarantees convergence for every pair of right-hand side and starting vector.

## Depends on

- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [Consistently ordered matrix](consistently-ordered-matrix.md)
- [Young's relation between SOR and Jacobi eigenvalues](young-sor-jacobi-eigenvalue-relation.md)

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), Theorem 4 and its proof (the case $w = 1$ of the relation $(\lambda + w - 1)^2 = \lambda w^2 \mu^2$), referring to J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997, Theorem 6.6. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.1, the general and specific convergence factors and the convergence rate $\tau = -\ln \rho$, and Section 4.2.5, the block form (4.42) and Theorem 4.16 with $\omega = 1$ ($\lambda = \mu^2$ for the nonzero eigenvalues $\lambda$ of the Gauss–Seidel matrix). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
