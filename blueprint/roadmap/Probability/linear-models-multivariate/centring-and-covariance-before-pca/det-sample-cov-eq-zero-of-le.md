# With $n \le p$ and $p \ge 1$, the sample covariance is singular

Let $X$ be a real $n \times p$ data matrix with at least one feature, $p \ge 1$, and no more samples
(rows) than features, $n \le p$, the usual regime of omics data. Then its
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$, where $X_c = X - \mathbf 1 \bar x^\top$, is singular:

$$\det S = 0.$$

Indeed $\operatorname{rank} S \le \max(n - 1, 0) < p$. The hypothesis $p \ge 1$ excludes the empty
$0 \times 0$ matrix, whose determinant is $1$.
