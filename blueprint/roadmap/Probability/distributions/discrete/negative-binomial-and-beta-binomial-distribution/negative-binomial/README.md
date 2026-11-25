# Negative binomial distribution

For real $r$ and $p$ and $k \in \mathbb{N}$, the negative binomial mass function is

$$\mathrm{NB}_{r, p}(k) = \frac{r^{(k)}}{k!} \, p^r (1 - p)^k,$$

with the rising factorial $r^{(k)} = r(r+1) \cdots (r+k-1)$ and the real power $p^r$, under the conventions $0^0 = 1$, $0^s = 0$ for $s \ne 0$ and $x^s = |x|^s \cos(\pi s)$ for $x < 0$. For $r > 0$ and $0 < p \le 1$ it is a probability mass function on $\mathbb{N}$.

## Idea

For a positive integer $r$, $\mathrm{NB}_{r, p}(k)$ is the probability of exactly $k$ failures before the $r$-th success in independent trials with success probability $p$; the rising factorial extends the count of arrangements to every real $r > 0$. In ecology and genomics the law is usually written with its size $\theta = r$ and its mean $\mu = \theta (1 - p)/p$, so that $p = \theta / (\theta + \mu)$. Its variance $\mu + \mu^2/\theta$ exceeds the mean when $\mu > 0$, which makes it a model for counts more dispersed than Poisson counts, and it puts at least as much mass at $0$ as the Poisson law with the same mean. At $\mu = 0$ it is the point mass at $0$.

## Statements

- [Negative binomial mass function with real shape](neg-binomial-pmf.md)
- [Negative binomial masses sum to one](has-sum-neg-binomial-pmf.md): basic property: normalisation
- [Negative binomial mass function with size and mean](neg-binomial-real.md): mean parametrisation
- [Mean parametrization of the negative binomial law](neg-binomial-real-eq-neg-binomial-pmf.md): agreement of the two parametrisations
- [Nonnegativity of the negative binomial mass function](neg-binomial-real-nonneg.md): basic property: nonnegativity (mean parametrisation)
- [Zero class of the negative binomial law](neg-binomial-real-zero.md): basic property: mass at zero
- [Negative binomial law with mean zero is a point mass](neg-binomial-real-mean-zero.md): degenerate case: mean zero gives the point mass at $0$
- [Normalization of the negative binomial law](has-sum-neg-binomial-real.md): basic property: normalisation (mean parametrisation)
- [Mean of the negative binomial law](has-sum-mul-neg-binomial-real.md): basic property: the mean
- [Second moment of the negative binomial law](has-sum-sq-neg-binomial-real.md): basic property: the second moment
- [Variance of the negative binomial law](variance-neg-binomial.md): basic property: the variance $\mu + \mu^2/\theta$
- [Zero class versus the Poisson law](exp-neg-le-neg-binomial-real-zero.md): comparison of the zero class with Poisson
