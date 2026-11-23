# Score of one count

A hyperparameter is a vector $\theta = (a, b) \in \mathbb{R}^2$ (prior shape $a$, prior rate $b$).
For a real size factor $\sigma$ and a count $k \in \mathbb{N}$, the score of one count is

$$
\psi_\sigma(\theta, k) = \Bigl(\psi_k(a) + \log b - \log(b + \sigma),\quad
\frac{a}{b} - \frac{a + k}{b + \sigma}\Bigr),
$$

with the [digamma increment](digamma-increment.md) $\psi_k(a) = \sum_{j < k} 1/(a + j)$, the real
logarithm ($\log 0 = 0$, $\log x = \log |x|$ for $x < 0$) and the convention $x / 0 = 0$. For
$\sigma > 0$ and $a, b > 0$ it is the [gradient](score-marginal-lik-eq-count-score.md) in $\theta$
of $\log P(k \mid a, b, \sigma)$, the logarithm of the
[marginal likelihood](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik.md) of one
count. Summed over a sample at a common size factor it gives the
[shape and rate scores](sum-count-score.md).
