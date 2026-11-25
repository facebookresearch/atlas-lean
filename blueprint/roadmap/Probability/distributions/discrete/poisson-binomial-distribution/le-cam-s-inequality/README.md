# Le Cam's inequality

Let $p \in [0, 1]^m$, let $\lambda = \sum_i p_i$, and let $\pi_p$ be the Poisson-binomial mass function.
Then the series $\sum_{j \ge 0} \bigl| \pi_p(j) - e^{-\lambda} \lambda^j / j! \bigr|$ converges and

$$\sum_{j=0}^{\infty} \Bigl| \pi_p(j) - e^{-\lambda} \frac{\lambda^j}{j!} \Bigr| \le 2 \sum_i p_i^2 .$$

## Idea

Many rare independent events give approximately Poisson counts, and Le Cam's inequality says how
closely: the total variation distance between the number of successes and the Poisson law with the
same mean, half the sum on the left, is at most $\sum_i p_i^2$. One proof couples each trial with a
Poisson variable of mean $p_i$ so that the two differ with probability at most $p_i^2$; another adds
the trials one at a time and compares the recurrences of the two mass functions. For $m$ equal
probabilities $\lambda/m$ the bound is $2\lambda^2/m$, which gives the Poisson limit of binomial laws.

## Statements

- [Le Cam's inequality](tsum-abs-poisson-binomial-pmf-sub-poisso.md)
- [Le Cam's inequality, finite truncations](sum-range-abs-poisson-binomial-pmf-sub-p.md): finite truncations, used in the proof

## Background

- [Poisson-binomial distribution](../poisson-binomial-law/README.md): the mass function

## Sources

- L. Le Cam, *An approximation theorem for the Poisson binomial distribution*, Pacific Journal of Mathematics, 1960.
