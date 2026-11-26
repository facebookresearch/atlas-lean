# GMRES iterate

For a real $n \times n$ matrix $A$, a right-hand side $b$, an initial guess $x_0$ with residual
$r_0 = b - Ax_0$ and a step $k$, a vector $x$ is a $k$-th GMRES iterate if
$x - x_0 \in \mathcal{K}_k(A, r_0) = \operatorname{span}\{r_0, Ar_0, \dots, A^{k-1} r_0\}$, the [Krylov subspace](../conjugate-gradient-method/krylov.md), and
$x$ minimizes $\|b - Ay\|_2$ over all $y \in x_0 + \mathcal{K}_k(A, r_0)$.

## Sources

- Y. Saad and M. H. Schultz, GMRES: a generalized minimal residual algorithm for solving nonsymmetric linear systems, SIAM J. Sci. Stat. Comput. 7 (1986), 856–869.
- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 35.
