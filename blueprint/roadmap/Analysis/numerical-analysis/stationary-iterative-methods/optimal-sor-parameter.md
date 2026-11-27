# Optimal SOR parameter

Let $A = \begin{pmatrix} D_1 & A_{12} \\ A_{21} & D_2 \end{pmatrix}$ be an $n \times n$ matrix whose diagonal blocks $D_1$ and $D_2$ are nonsingular diagonal matrices. Suppose that all eigenvalues of its Jacobi iteration matrix $G_J$ are real and that $\mu = \rho(G_J) < 1$. Then among nonzero real parameters $\omega$ the spectral radius of the [SOR iteration matrix](sor-iteration.md) $G_\omega$ is smallest for

$$\omega_{\mathrm{opt}} = \frac{2}{1 + \sqrt{1 - \mu^2}}, \qquad \text{with} \qquad \rho(G_{\omega_{\mathrm{opt}}}) = \omega_{\mathrm{opt}} - 1 = \frac{\mu^2}{\bigl(1 + \sqrt{1 - \mu^2}\bigr)^2}.$$

For the five-point discretization of Poisson's equation with Dirichlet boundary data on the uniform square grid with $n$ interior points in each direction, in red-black order, $\mu = \cos(\pi/(n+1))$, and $\rho(G_{\omega_{\mathrm{opt}}}) \approx 1 - 2\pi/(n+1)$, against $\rho(G_J) \approx 1 - \pi^2/(2(n+1)^2)$.

## Depends on

- [Successive overrelaxation](sor-iteration.md)
- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [Consistently ordered matrix](consistently-ordered-matrix.md)
- [Young's relation between SOR and Jacobi eigenvalues](young-sor-jacobi-eigenvalue-relation.md)

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), Theorem 5 and the analysis of Jacobi for the model problem, referring for the proof (solving Young's relation for $\lambda$) to J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997, Theorem 6.7. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
