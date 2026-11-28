# Sample covariance as $(n-1)^{-1}(X^\top X - n\bar x\bar x^\top)$

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with column means
$\bar x$
([sample means](../principal-component-analysis/col-mean.md)).
For every $n$, the
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$, where $X_c = X - \mathbf 1 \bar x^\top$, is

$$S = (n - 1)^{-1} \bigl(X^\top X - n\, \bar x \bar x^\top\bigr).$$

The divisor $n - 1$ is meaningful for $n \ge 2$. For $n = 1$ the factor is $0^{-1}$, which is $0$ by
convention, so both sides are $0$.
