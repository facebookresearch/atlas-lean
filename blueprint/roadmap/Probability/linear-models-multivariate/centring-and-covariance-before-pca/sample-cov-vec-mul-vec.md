# $S(u v^\top)$ is the sample variance of $u$ times $v v^\top$

Let $u \in \mathbb{R}^n$ and $v \in \mathbb{R}^p$, let $\bar u = \frac1n \sum_k u_k$, and write
$S(Y)$ for the
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
of a data matrix $Y$. For every $n$,

$$S(u v^\top) = s_u^2\, v v^\top, \qquad s_u^2 = (n-1)^{-1} \sum_{i=1}^n (u_i - \bar u)^2,$$

where $s_u^2$ is the sample variance of the entries of $u$. For $n = 1$ the factor $(n-1)^{-1}$ is
$0^{-1} = 0$ by convention, and for $n = 0$ the sum is empty, so $s_u^2 = 0$ for $n \le 1$. In
particular $S(u v^\top)$ has [rank at most one](rank-sample-cov-vec-mul-vec-le.md).
