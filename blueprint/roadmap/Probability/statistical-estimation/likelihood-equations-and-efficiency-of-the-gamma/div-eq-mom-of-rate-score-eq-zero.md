# Every root of the rate equation shares the moment fitted mean

Let $\iota$ be a finite nonempty set of $n \ge 1$ observations, with counts $k_i \in \mathbb{N}$ and
size factors $s_i$. Let the size factors equal a common value, $s_i = \sigma$ for every $i$, with
$\sigma > 0$, let the [sample mean](count-mean.md) $M$ be positive and let $V > M$ be real. If $a$
is real, $b > 0$ and $(a, b)$ solves the [rate score](rate-score.md) equation $S_b(a, b) = 0$, then
its plug-in prior mean is

$$\frac{a}{b} = \frac{M}{\sigma} = \frac{\hat a_{\mathrm{mom}}}{\hat b_{\mathrm{mom}}},$$

also the plug-in prior mean of the
[moment shape](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-shape.md)
$\hat a_{\mathrm{mom}} = M^2 / (V - M)$ and
[moment rate](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-rate.md)
$\hat b_{\mathrm{mom}} = \sigma M / (V - M)$. The two estimators differ in the shape equation: for
$a > 0$ a root of both score equations solves $\sum_i \psi_{k_i}(a) = n \log(1 + M / a)$, the moment
estimator $M + M^2 / a = V$.
