# With at most one sample, the centred data matrix is zero

Let $X$ be a real $n \times p$ data matrix with $n \le 1$ rows (samples). Its
[centred matrix](../principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$ is the zero matrix: for $n = 1$ the single sample equals its mean,
and for $n = 0$ there are no rows.
