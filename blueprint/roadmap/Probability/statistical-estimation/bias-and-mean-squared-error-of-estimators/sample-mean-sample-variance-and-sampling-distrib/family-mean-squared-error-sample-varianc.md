# Mean squared error of the sample variance is its variance

Let $X_0, X_1, \dots$ be independent, identically distributed, square-integrable real random variables on a probability space $(\Omega, \mu)$, let $n \ge 2$, and let $s^2_n = \frac{1}{n-1}\sum_{i<n}(X_i - \bar X_n)^2$ be the sample variance of the first $n$ observations, $\bar X_n = \frac1n\sum_{i<n} X_i$. Suppose also that $s^2_n$ is square integrable and $(s^2_n - \operatorname{Var}(X_0))^2$ is integrable. Then the mean squared error of $s^2_n$ as an estimator of $\operatorname{Var}(X_0)$ equals its variance:

$$\mathbb{E}\big[(s^2_n - \operatorname{Var}(X_0))^2\big] = \operatorname{Var}(s^2_n).$$
