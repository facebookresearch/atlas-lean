# Quadratic accuracy of the Rayleigh quotient

Let $T$ be a symmetric linear operator on a real inner product space, and let $Tq = \lambda q$.
Then for every vector $v$,
$\langle v, Tv\rangle - \lambda\|v\|^2 = \langle v - q, (T - \lambda)(v - q)\rangle$.
Hence, if $q \ne 0$ and $T$ is bounded (for instance on a finite-dimensional space), the Rayleigh
quotient $r(v) = \langle v, Tv\rangle/\|v\|^2$ satisfies $r(v) - \lambda = O(\|v - q\|^2)$ as
$v \to q$: it is a quadratically accurate estimate of the eigenvalue. The condition $q \ne 0$ is needed: for $T = I$, $\lambda = 0$ and $q = 0$, $r(v) - \lambda = 1$ for every $v \ne 0$.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 27.
