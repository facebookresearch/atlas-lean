# Sample covariance has rank at most $n - 1$

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$, where $X_c = X - \mathbf 1 \bar x^\top$. For every $n$,

$$\operatorname{rank} S \le n - 1,$$

where $n - 1$ is truncated subtraction, $0$ for $n = 0$. For $n \le 1$, $S = 0$.
