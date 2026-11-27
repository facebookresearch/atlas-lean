# Composition of relative errors

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. If $a, b$ are natural numbers with $(a + b)\,u < 1$, then

$$(1 + \gamma_a)(1 + \gamma_b) \le 1 + \gamma_{a+b}.$$
