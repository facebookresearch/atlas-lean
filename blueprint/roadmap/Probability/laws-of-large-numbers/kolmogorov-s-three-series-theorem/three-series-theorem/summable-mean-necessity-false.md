# Convergent series whose truncated means are not absolutely summable

There are a sequence $X_0, X_1, \dots$ of real random variables on a one-point probability space
and a threshold $A > 0$ such that the $X_n$ are measurable and independent, the partial sums
$\sum_{i < n} X_i$ converge, the partial sums of the [truncations](../truncation/truncated-rv.md)
$Y_i = X_i \mathbf{1}_{\{|X_i| \le A\}}$ converge, and yet the series of truncated means
$\sum_n \mathbb{E}[Y_n]$ does not converge absolutely. One example is the deterministic sequence
$X_k = (-1)^k / (k + 1)$ with $A = 1$: it agrees with its truncations, has all variances $0$, and
its means $(-1)^k / (k + 1)$ form a convergent but not absolutely convergent series. So in the
necessity half of the three-series theorem only the convergence of the partial sums of the
truncated means can be concluded, as in [the mean and variance step](three-series-necessity-mean-variance.md).
