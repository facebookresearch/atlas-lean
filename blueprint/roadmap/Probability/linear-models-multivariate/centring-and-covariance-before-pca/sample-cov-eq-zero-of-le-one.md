# With at most one sample, the sample covariance is zero

Let $X$ be a real $n \times p$ data matrix with $n \le 1$ rows (samples). Its
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$ is the zero matrix, because the centred matrix
$X_c = X - \mathbf 1 \bar x^\top$ is zero.
