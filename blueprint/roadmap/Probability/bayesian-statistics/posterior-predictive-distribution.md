# The posterior predictive distribution

Let $\pi$ be a prior probability on a standard Borel parameter space $\Theta$, let $P_\theta$ and $Q_\theta$ be Markov kernels from $\Theta$ to standard Borel observation spaces, and let $(\theta, X, Y)$ have the law $\pi(d\theta)P_\theta(dx)Q_\theta(dy)$, so that $X$ and $Y$ are conditionally independent given $\theta$. Let $\pi(d\theta \mid x)$ be a regular version of the posterior. Then $B \mapsto \int Q_\theta(B)\,\pi(d\theta \mid x)$ is a version of the conditional law of $Y$ given $X = x$: the equality holds for almost every $x$ under the marginal law of $X$, not for every $x$.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Existence and almost-sure uniqueness of regular conditional distributions on standard Borel spaces.

## Sources

- A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data Analysis*, 3rd ed., CRC Press, 2013, Section 1.3, equation (1.4), <http://www.stat.columbia.edu/~gelman/book/BDA3.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
