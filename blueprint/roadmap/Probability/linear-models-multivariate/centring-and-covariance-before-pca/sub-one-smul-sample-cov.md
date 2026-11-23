# Sample covariance times $n - 1$ is $X^\top X - n\bar x\bar x^\top$

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with column means
$\bar x$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md)),
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$ and
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$. For every $n$,

$$(n - 1)\, S = X^\top X - n\, \bar x \bar x^\top.$$

For $n = 1$ both sides vanish: the left side because of the factor $n - 1 = 0$, the right side
because the single sample equals its mean. For $n = 0$ both sides are the zero matrix.
