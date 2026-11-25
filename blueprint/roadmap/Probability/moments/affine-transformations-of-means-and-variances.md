# Means and variances under affine change of scale

Let $X$ and $Y$ be integrable random variables and $a, b$ real numbers. Then $E[aX + b] = aE[X] + b$; if $X$ is square-integrable, $\operatorname{Var}(aX + b) = a^2\operatorname{Var}(X)$. Differences of means transform by the factor $a$ alone: $E[aX + b] - E[aY + b] = a(E[X] - E[Y])$. Ratios of means are invariant under scaling, $E[aX]/E[aY] = E[X]/E[Y]$ for $a \ne 0$ and $E[Y] \ne 0$, but a shift can change them (for constants $X = 1$, $Y = 2$ and $b = 1$, $1/2$ becomes $2/3$), though not always (a ratio equal to $1$ is preserved). Ratios of differences of means, $(E[X] - E[Y])/(E[U] - E[W])$ for integrable $X, Y, U, W$ with a nonzero denominator, are invariant under every map $v \mapsto av + b$ with $a \ne 0$ applied to all four variables.

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, 2nd rev. ed., American Mathematical Society, 1997, Theorem 6.2 and Theorem 6.7, <https://math.dartmouth.edu/~prob/prob/prob.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
