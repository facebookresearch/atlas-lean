# $3\gamma_n + \gamma_n^2 \le \gamma_{3n}$

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. If $n$ is a natural number with $3nu < 1$, then

$$3\gamma_n + \gamma_n^2 \le \gamma_{3n},$$

since $1 + 3\gamma_n + \gamma_n^2 \le (1 + \gamma_n)^3 \le 1 + \gamma_{3n}$. It converts the [backward stability bound of Gaussian elimination](exists-add-mul-vec-eq-of-is-fl-lu.md) into its usual $\gamma_{3n}$ form.

## Informally uses

- [Composition of relative errors](one-add-gamma-mul-le.md): applied twice, $(1 + \gamma_n)(1 + \gamma_n) \le 1 + \gamma_{2n}$ and $(1 + \gamma_{2n})(1 + \gamma_n) \le 1 + \gamma_{3n}$.
