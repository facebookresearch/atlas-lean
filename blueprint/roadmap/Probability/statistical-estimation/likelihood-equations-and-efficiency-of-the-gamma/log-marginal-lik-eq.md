# Closed form of one log marginal likelihood term

For $a, b, s > 0$ and every count $k \in \mathbb{N}$, the logarithm of the
[marginal likelihood](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik.md) is

$$
\log P(k \mid a, b, s) = \sum_{j < k} \log(a + j) + k \log s - \log k! +
a \log b - (a + k) \log(b + s).
$$
