# Sample covariance is $\frac{n}{n-1}$ times the empirical covariance

Let $X$ be a real $n \times p$ data matrix whose rows are $n \ge 2$ samples, with column means
$\bar x$
([sample means](../principal-component-analysis/col-mean.md)).
The
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
$S = (n-1)^{-1} X_c^\top X_c$, where $X_c = X - \mathbf 1 \bar x^\top$, is

$$S = \frac{n}{n-1} \Bigl(\frac1n X^\top X - \bar x \bar x^\top\Bigr),$$

with $\frac1n X^\top X$ the [uncentred second-moment matrix](second-moment.md). The bracket is the
covariance matrix of the empirical distribution of the samples (divisor $n$); the factor
$\frac{n}{n-1}$, Bessel's correction, turns it into the sample covariance (divisor $n - 1$).
