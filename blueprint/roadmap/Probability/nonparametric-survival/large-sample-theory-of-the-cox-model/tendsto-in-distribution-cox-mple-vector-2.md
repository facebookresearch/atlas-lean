# Asymptotic normality of the vector Cox estimator

For each $n$ let survival data with covariate vectors in $\mathbb{R}^p$ be random, with Cox score vector $U_n$, observed information matrix $I_n$, and $\hat\beta_n$ a maximizer of the log partial likelihood whenever one exists. Assume the vector Andersen–Gill conditions: $U_n(\beta_0)/\sqrt n \Rightarrow Z$; $I_n(b)/n \to \Sigma(b)$ entrywise, uniformly on a closed ball of radius $r > 0$ about $\beta_0$, in probability; $\Sigma$ continuous at $\beta_0$; and $\Sigma(\beta_0)$ positive definite. If $\hat\beta_n$ is measurable and $Z \sim N(0, \Sigma(\beta_0))$, then $\sqrt n(\hat\beta_n - \beta_0)$ converges in distribution to $N(0, \Sigma(\beta_0)^{-1})$.

## Sources

- P. K. Andersen and R. D. Gill, "Cox's regression model for counting processes: a large sample study", Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3.
