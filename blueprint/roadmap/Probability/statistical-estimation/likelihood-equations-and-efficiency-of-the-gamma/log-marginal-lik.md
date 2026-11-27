# Log marginal likelihood of the hyperparameters

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For real hyperparameters $a$ (prior shape) and $b$ (prior rate), the log marginal likelihood
is

$$\ell(a, b) = \sum_{i \in \iota} \log P(k_i \mid a, b, s_i),$$

where $P(k \mid a, b, s)$ is the
[marginal likelihood](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik.md) of the
count $k$ under the hierarchy $k \mid \lambda \sim \mathrm{Po}(s \lambda)$,
$\lambda \sim \mathrm{Gamma}(a, b)$, one rate $\lambda_i$ per observation. The logarithm is real
with the conventions $\log 0 = 0$ and $\log x = \log |x|$ for $x < 0$. For $a, b > 0$ and $s \ge 0$,
$P(k \mid a, b, s)$ is the negative binomial probability $\mathrm{NB}(a, s a / b)$ of $k$; with
positive size factors $s_i > 0$ every term is then the logarithm of a positive probability and, the
counts being independent with one rate each, $\ell$ is the log-likelihood of the sample. A size
factor $0$ with a positive count gives probability $0$, which the convention $\log 0 = 0$ scores as
$0$.
