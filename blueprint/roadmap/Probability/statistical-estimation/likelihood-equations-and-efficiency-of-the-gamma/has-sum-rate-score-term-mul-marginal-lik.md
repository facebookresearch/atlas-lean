# The rate score is unbiased

For $a > 0$, $b > 0$ and a size factor $s \ge 0$, the rate score term of one count has mean $0$
under the [marginal law](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik.md)
$P(k \mid a, b, s) = \mathrm{NB}(a, s a / b)$ of the hierarchy:

$$\sum_{k = 0}^{\infty} \Bigl(\frac{a}{b} - \frac{a + k}{b + s}\Bigr) P(k \mid a, b, s) = 0,$$

the series converging. The rate score equation is Fisher consistent.
