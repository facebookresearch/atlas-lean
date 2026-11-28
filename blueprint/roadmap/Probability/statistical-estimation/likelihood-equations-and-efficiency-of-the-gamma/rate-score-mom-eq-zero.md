# Method of moments solves the rate score equation

Let $\iota$ be a finite nonempty set of $n \ge 1$ observations, with counts $k_i \in \mathbb{N}$ and
size factors $s_i$. Let the size factors equal a common value, $s_i = \sigma$ for every $i$, with
$\sigma > 0$, let the [sample mean](count-mean.md) $M$ be positive, and let $V > M$ be real, for
example the [biased sample variance](count-var.md) of an overdispersed sample. Then the
[moment shape](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-shape.md)
$\hat a_{\mathrm{mom}} = M^2 / (V - M)$ and the
[moment rate](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-rate.md)
$\hat b_{\mathrm{mom}} = \sigma M / (V - M)$ solve the [rate score](rate-score.md) equation:
$S_b(\hat a_{\mathrm{mom}}, \hat b_{\mathrm{mom}}) = 0$.
