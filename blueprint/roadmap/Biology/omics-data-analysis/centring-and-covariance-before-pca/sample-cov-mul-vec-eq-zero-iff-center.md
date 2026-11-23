# Sample covariance and centred data have the same null vectors

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c$ and
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$. For every $n$ and every $w \in \mathbb{R}^p$,

$$S w = 0 \iff X_c w = 0.$$

For $n \le 1$ both sides hold for every $w$, since $S = 0$ and $X_c = 0$.
