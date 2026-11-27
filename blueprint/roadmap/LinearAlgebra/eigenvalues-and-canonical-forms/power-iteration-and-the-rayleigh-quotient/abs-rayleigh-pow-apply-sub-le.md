# The power-iteration eigenvalue estimate converges twice as fast

Under the hypotheses of the unnormalized bound, if $|\lambda_j - \lambda_{i_0}| \le D$ for every
$j$, then the Rayleigh quotient of $x = T^k v_0$ satisfies
$|\langle x, Tx\rangle/\|x\|^2 - \lambda_{i_0}| \le D\rho^{2k}(\|v_0\|/|c|)^2$.

## Informally uses

- [Power iteration converges linearly (unnormalized form)](norm-smul-pow-apply-sub-le.md): the eigenvector error bound, squared.

## Background

- [Quadratic accuracy of the Rayleigh quotient](inner-apply-sub-eq-of-eigen.md): the same quadratic-accuracy phenomenon.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 27 (convergence of power iteration).
