# Rounding error relative to the rounded value

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. If $u < 1$, that is $p \ge 1$, then for every $x \in K$

$$|\mathrm{fl}(x) - x| \le \gamma_1\,|\mathrm{fl}(x)|, \qquad \gamma_1 = \frac{u}{1 - u}.$$

The rounding error is thus bounded relative to the rounded value rather than to $x$.
