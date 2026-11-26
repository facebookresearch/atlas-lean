# Mean-zero data: sample covariance is $n/(n-1)$ times the second moment

Let $X$ be a real $n \times p$ data matrix whose rows are $n \ge 2$ samples, with every column mean
zero ($\bar x = 0$,
[sample means](../principal-component-analysis/col-mean.md)).
Then the
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
is

$$S = \frac{n}{n-1} \cdot \frac1n X^\top X = \frac{1}{n-1} X^\top X.$$

It differs from the [uncentred second-moment matrix](second-moment.md) $\frac1n X^\top X$ only by
the factor $\frac{n}{n-1}$.
