# Asymptotic normality of the vector Cox estimator

For each $n$ let survival data with covariate vectors in $\mathbb{R}^p$ be random, with Cox score vector $U_n$, observed information matrix $I_n$, and $\hat\beta_n$ a maximizer of the log partial likelihood whenever one exists. Assume the vector Andersen–Gill conditions: $U_n(\beta_0)/\sqrt n \Rightarrow Z$; for some $r > 0$ and every $\eta > 0$, the outer probability that $|I_n(b)_{jk}/n - \Sigma(b)_{jk}| \ge \eta$ for some $b$ with $\|b - \beta_0\|_\infty \le r$ and some entry $(j, k)$ tends to $0$; $\Sigma$ continuous at $\beta_0$; and $\Sigma(\beta_0)$ positive definite. If $\hat\beta_n$ is almost everywhere measurable and $Z \sim N(0, \Sigma(\beta_0))$, then $\sqrt n(\hat\beta_n - \beta_0)$ converges in distribution to $N(0, \Sigma(\beta_0)^{-1})$.

## Sources

- P. K. Andersen and R. D. Gill, "Cox's regression model for counting processes: a large sample study", Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3.
