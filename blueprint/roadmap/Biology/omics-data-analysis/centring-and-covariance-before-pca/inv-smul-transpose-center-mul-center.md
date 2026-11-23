# Empirical covariance is the second moment minus the mean outer product

Let $X$ be a real $n \times p$ data matrix whose rows are $n \ge 1$ samples, with column means
$\bar x$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md))
and
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$. Then

$$\frac1n X_c^\top X_c = \frac1n X^\top X - \bar x \bar x^\top,$$

where $\frac1n X^\top X$ is the [uncentred second-moment matrix](second-moment.md). The left side,
with divisor $n$ instead of the divisor $n - 1$ of the
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md),
is the covariance matrix of the empirical distribution of the samples, which gives mass $\frac1n$ to
each row.
