# Power iteration converges linearly (unnormalized form)

Let $(b_j)$ be an orthonormal eigenbasis of $T$ on a finite-dimensional real inner product space,
$T b_j = \lambda_j b_j$, let $q = b_{i_0}$ with $\lambda_{i_0} \ne 0$, let $\mu \ge 0$ with
$|\lambda_j| \le \mu$ for $j \ne i_0$, and let $v_0$ have $c = \langle q, v_0\rangle \ne 0$. Then
for every $k$,
$\|(c\lambda_{i_0}^k)^{-1} T^k v_0 - q\| \le \rho^k \|v_0\| / |c|$ with $\rho = \mu/|\lambda_{i_0}|$.
When $\lambda_{i_0}$ is strictly dominant ($\rho < 1$) the error decays linearly at rate
$|\lambda_2/\lambda_1|$.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 27 (convergence of power iteration).
