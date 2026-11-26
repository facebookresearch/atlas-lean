# Jacobi and Gauss–Seidel converge for irreducibly diagonally dominant matrices

Let $A$ be an [irreducible](irreducible-matrix.md) $n \times n$ complex matrix that is weakly row diagonally dominant, $|a_{ii}| \ge \sum_{j \ne i} |a_{ij}|$ for every $i$, with strict inequality for at least one $i$. Then the [Jacobi and Gauss–Seidel iteration matrices](jacobi-and-gauss-seidel-iteration-matrices.md) have spectral radius less than $1$, so both iterations for $Ax = b$ converge to the solution for every $b$ and every starting vector.

Weak diagonal dominance alone is not enough: $A = \begin{pmatrix} 1 & -1 & 0 \\ 1 & 1 & 0 \\ 0 & 0 & 1 \end{pmatrix}$ is weakly row diagonally dominant with strict inequality in its last row, but reducible, and its Jacobi matrix has eigenvalues $\pm i$ and $0$. The diagonal entries of an irreducibly diagonally dominant matrix are nonzero, so both iterations are defined. The theorem does not order the two spectral radii: for $A = I - J$ with $8J = \begin{pmatrix} 0 & 2 & 2 \\ 1 & 0 & 2 \\ 1 & -2 & 0 \end{pmatrix}$, a real irreducible strictly row diagonally dominant matrix, the Jacobi matrix $J$ satisfies $J^3 = 0$, while the Gauss–Seidel matrix has trace $-1/128$ and so a nonzero spectral radius.

## Depends on

- [Irreducible matrix](irreducible-matrix.md)
- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [Irreducibly diagonally dominant matrices are nonsingular](irreducibly-diagonally-dominant-matrices-are-nonsingular.md)
- [Convergence of stationary iterations](convergence-of-stationary-iterations.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.3, Theorem 4.9 and its proof for irreducibly diagonally dominant matrices: the row-sum argument gives $\rho \le 1$, and an eigenvalue of modulus $1$ would make $N - \lambda M$ a singular irreducibly diagonally dominant matrix. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), the counterexample before the definition of irreducibility, and Theorem 2, whose sharper claim $\rho(R_{GS}) < \rho(R_J) < 1$ (cited there from J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997, Theorem 6.3) does not hold under these hypotheses, by the example above. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
