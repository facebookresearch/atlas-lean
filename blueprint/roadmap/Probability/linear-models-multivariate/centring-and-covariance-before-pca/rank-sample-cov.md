# Sample covariance has the same rank as the centred data matrix

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c$ and
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$. For every $n$,

$$\operatorname{rank} S = \operatorname{rank} X_c.$$

For $n \le 1$ both ranks are $0$, since $S = 0$ and $X_c = 0$; for $n \ge 2$ the factor $(n-1)^{-1}$
is nonzero and $\operatorname{rank}(X_c^\top X_c) = \operatorname{rank} X_c$.
