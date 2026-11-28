# Overdispersion gives a solution of the score equations

Let $\iota$ be a finite nonempty set of $n \ge 1$ observations, with counts $k_i \in \mathbb{N}$ and
size factors $s_i$. Let the size factors equal a common value, $s_i = \sigma$ for every $i$, with
$\sigma > 0$, and let the sample be overdispersed: $0 < M < V$ for its [sample mean](count-mean.md)
$M$ and [biased sample variance](count-var.md) $V$. For $M > 0$ this is exactly the condition under
which the [moment estimates](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-shape.md) are
positive. Then the score equations have a solution with both coordinates positive: $S_a(a, b) = 0$
and $S_b(a, b) = 0$ for some $a, b > 0$, where $S_a$ and $S_b$ are the [shape](shape-score.md) and
[rate](rate-score.md) scores; by the [joint score equations](score-eq-zero-iff-const.md) such a root
has $b = \sigma a / M$. It is the
[unique](../existence-and-uniqueness-of-the-gamma-poisson-ml/exists-unique-score-root.md) positive
solution.
