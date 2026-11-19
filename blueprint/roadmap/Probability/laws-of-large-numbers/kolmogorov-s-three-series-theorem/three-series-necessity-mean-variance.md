# Kolmogorov three-series necessity, series (2)–(3)

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be independent measurable real random
variables whose partial sums $\sum_{i < n} X_i$ converge almost surely, and let $A > 0$. Then the
[truncations](truncated-rv.md) $Y_n = X_n \mathbf{1}_{\{|X_n| \le A\}}$ satisfy: the partial sums
$\sum_{k < n} \mathbb{E}[Y_k]$ converge to a finite limit, and
$\sum_n \operatorname{Var}(Y_n) < \infty$. The means themselves need not form an absolutely
convergent series ([counterexample](summable-mean-necessity-false.md)). Series (1),
$\sum_n P(|X_n| > A) < \infty$, is the [tail-probability step](summable-tail-prob-of-ae-tendsto.md).
