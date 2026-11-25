# Growth of $\gamma$ by one rounding

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. If $k$ is a natural number with $(k + 1) u < 1$, then

$$u + (1 + u)\,\gamma_k \le \gamma_{k+1}.$$

It bounds the relative error after one more rounding of a quantity already carrying relative error $\gamma_k$.
