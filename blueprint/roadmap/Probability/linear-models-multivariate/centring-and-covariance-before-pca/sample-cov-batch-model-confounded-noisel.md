# Noiseless confounded design: closed form of the sample covariance

Let $\mu, \beta, \delta \in \mathbb{R}^p$ and $b \in \mathbb{R}^n$, and let
$X = \mathbf 1 \mu^\top + b \beta^\top + b \delta^\top$ be the confounded
[additive design](batch-model.md) without residual noise ($E = 0$). For every $n$, its
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
is

$$S = s_b^2\, (\beta + \delta)(\beta + \delta)^\top, \qquad
s_b^2 = (n-1)^{-1} \sum_{i=1}^n (b_i - \bar b)^2, \quad \bar b = \frac1n \sum_k b_k.$$

For $n = 1$ the factor $(n-1)^{-1}$ is $0^{-1} = 0$ by convention, and for $n = 0$ the sum is empty,
so $s_b^2 = 0$ for $n \le 1$. Only the combined effect $\beta + \delta$ enters $S$, not its split
into batch effect and biological signal. When $b$ is not constant, $s_b^2 > 0$, so $S \ne 0$ exactly
when $\beta + \delta \ne 0$. $S$ has
[rank at most one](rank-sample-cov-batch-model-confounded-n.md), so it is singular when $p \ge 2$.
