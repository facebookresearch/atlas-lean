# Gauss–Seidel converges for strictly diagonally dominant matrices

Let $A$ be an $n \times n$ real or complex matrix that is strictly row diagonally dominant, $|a_{ii}| > \sum_{j \ne i} |a_{ij}|$ for every $i$. Then the [Jacobi and Gauss–Seidel iteration matrices](jacobi-and-gauss-seidel-iteration-matrices.md) satisfy

$$\|G_{GS}\|_\infty \le \|G_J\|_\infty < 1,$$

where $\|\cdot\|_\infty$ is the operator norm induced by the maximum norm. Hence both the Jacobi and the Gauss–Seidel iterations for $Ax = b$ converge to the solution, for every $b$ and every starting vector.

Here $\|G_J\|_\infty = \max_i \sum_{j \ne i} |a_{ij}|/|a_{ii}|$; the convergence of the Jacobi iteration is the [Jacobi convergence theorem](../../../LinearAlgebra/matrix-decompositions/jacobi-method/jacobi-iteration-converges.md).

## Depends on

- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [Convergence of stationary iterations](convergence-of-stationary-iterations.md)

## Related topics

- [Jacobi convergence theorem](../../../LinearAlgebra/matrix-decompositions/jacobi-method/jacobi-iteration-converges.md)

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), Theorem 1 (strict row diagonal dominance gives $\|R_{GS}\|_\infty \le \|R_J\|_\infty < 1$), referring for the full proof to J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997, Theorem 6.2. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.3, Theorem 4.9 and its proof for strictly diagonally dominant matrices, which bounds the eigenvalues of both iteration matrices by row sums. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
