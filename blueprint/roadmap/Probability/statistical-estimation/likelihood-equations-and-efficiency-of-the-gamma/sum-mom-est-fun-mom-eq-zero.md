# The moment estimate solves the moment estimating equations

Let $\sigma$ be real, let $k_0, \dots, k_{n - 1}$ be counts with sample mean
$M = n^{-1} \sum_{i < n} k_i$ and biased sample variance $V = n^{-1} \sum_{i < n} k_i^2 - M^2$, and
let $0 < M < V$ (so $n \ge 1$). Then the moment estimates $\hat a = M^2 / (V - M)$ and
$\hat b = \sigma M / (V - M)$, the
[moment shape](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-shape.md) and
[moment rate](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-rate.md), solve the moment
estimating equations: $\sum_{i < n} g_\sigma\bigl((\hat a, \hat b), k_i\bigr) = 0$ for the
[moment estimating function](mom-est-fun.md).
