# Means and variances under affine change of scale

Let $X$ and $Y$ be integrable real random variables on a probability space and let $a,b$ be real numbers. Then $E[aX + b] = aE[X] + b$; if $X$ is square-integrable, $\operatorname{Var}(aX + b) = a^2\operatorname{Var}(X)$. Differences of means transform by the factor $a$ alone: $E[aX + b] - E[aY + b] = a(E[X] - E[Y])$.

Ratios of means are invariant under scaling: $E[aX]/E[aY] = E[X]/E[Y]$ if $a \ne 0$ and $E[Y] \ne 0$. A shift can change the ratio: for constants $X = 1$, $Y = 2$ and $b = 1$, it changes from $1/2$ to $2/3$. A ratio equal to $1$ is preserved under an affine change whenever both the original and transformed denominators are nonzero.

Ratios of differences of means, $(E[X] - E[Y])/(E[U] - E[W])$ for integrable $X,Y,U,W$ with a nonzero denominator, are invariant under every map $v \mapsto av + b$ with $a \ne 0$ applied to all four variables.

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, Dartmouth PDF dated July 4, 2006, Theorems 6.2 and 6.7, <https://math.dartmouth.edu/~prob/prob/prob.pdf>. These give the discrete expectation and variance cases. The laws above use an arbitrary probability measure, and the ratio identities follow algebraically.
