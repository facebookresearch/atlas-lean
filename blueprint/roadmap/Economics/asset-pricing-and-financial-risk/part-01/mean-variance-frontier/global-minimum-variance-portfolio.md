# The global minimum-variance portfolio

Let $n \ge 1$ and let $\Sigma$ be a positive definite $n \times n$ covariance matrix and $\mathbf 1$ the all-ones vector. Among weights $w$ with $\mathbf 1^{\mathsf T}w = 1$, the variance $w^{\mathsf T}\Sigma w$ has the unique minimizer $w^* = \Sigma^{-1}\mathbf 1/(\mathbf 1^{\mathsf T}\Sigma^{-1}\mathbf 1)$, with minimum value $1/(\mathbf 1^{\mathsf T}\Sigma^{-1}\mathbf 1)$.

Proof. $\mathbf 1^{\mathsf T}\Sigma^{-1}\mathbf 1 > 0$ because $\Sigma^{-1}$ is positive definite, so $w^*$ is defined and feasible. Any feasible $w$ is $w^* + d$ with $\mathbf 1^{\mathsf T}d = 0$. Since $\Sigma w^*$ is a multiple of $\mathbf 1$, $d^{\mathsf T}\Sigma w^* = 0$, hence $w^{\mathsf T}\Sigma w = w^{*\mathsf T}\Sigma w^* + d^{\mathsf T}\Sigma d$, and $d^{\mathsf T}\Sigma d > 0$ for $d \ne 0$.

## Background

- [Existence and uniqueness of the minimum-variance portfolio](exists-unique-min-variance.md): the minimum-variance portfolio for a target expected return.

## Sources

- R. C. Merton, "An analytic derivation of the efficient portfolio frontier", *Journal of Financial and Quantitative Analysis* 7(4):1851–1872, 1972, discussion around equations (29)–(30), <http://www.stat.ucla.edu/~nchristo/statistics_c183_c283/analytic_derivation_frontier.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
