# The per-count score is the gradient of the log marginal likelihood

Let $\sigma > 0$ and $\theta = (a, b)$ with $a, b > 0$. For every count $k \in \mathbb{N}$, the
[score of one count](count-score.md) is the gradient at $\theta$ of
$(a', b') \mapsto \log P(k \mid a', b', \sigma)$, the logarithm of the
[marginal likelihood](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik.md), the
negative binomial probability $\mathrm{NB}(a', \sigma a' / b')$ of $k$:

$$\nabla_\theta \log P(k \mid a, b, \sigma) = \psi_\sigma(\theta, k).$$
