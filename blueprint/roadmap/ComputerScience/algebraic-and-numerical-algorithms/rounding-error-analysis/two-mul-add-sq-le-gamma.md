# Two roundings stay within $\gamma_{k+1}$

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. If $k \ge 1$ is a natural number with $(k + 1) u < 1$, then

$$2u + u^2 \le \gamma_{k+1}.$$

Indeed $2u + u^2 \le \gamma_2 \le \gamma_{k+1}$: two successive roundings, of relative error at most $u$ each, stay within $\gamma_{k+1}$.
