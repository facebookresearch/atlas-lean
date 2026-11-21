# Orthogonality of martingale increments

Let $(\Omega, \mu)$ be a probability space with a filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$, and let $(X_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$ with $\mathbb{E}[X_k^2] < \infty$ for every $k$. If $m \le n$ and $Y$ is an $\mathcal{F}_m$-measurable real random variable with $\mathbb{E}[Y^2] < \infty$, then $\mathbb{E}[(X_n - X_m) Y] = 0$: the increment $X_n - X_m$ is orthogonal in $L^2$ to every square-integrable $\mathcal{F}_m$-measurable random variable.

## Idea

In $L^2$, conditional expectation given $\mathcal{F}_m$ is the orthogonal projection onto the square-integrable $\mathcal{F}_m$-measurable variables, and the martingale property says that $X_m$ is the projection of $X_n$. The increment $X_n - X_m$ is the residual of this projection, so it is orthogonal to that subspace. Taking $Y = X_m$ gives the Pythagorean identity $\mathbb{E}[(X_n - X_m)^2] = \mathbb{E}[X_n^2] - \mathbb{E}[X_m^2]$: second moments increase, and increments over disjoint time intervals are uncorrelated, like the steps of a random walk. Its conditional form is $\mathbb{E}[(X_n - X_m)^2 \mid \mathcal{F}_m] = \mathbb{E}[X_n^2 \mid \mathcal{F}_m] - X_m^2$. These identities make a square-integrable martingale behave like a sum of orthogonal vectors, which underlies its $L^2$ convergence and the construction of stochastic integrals.

## Statements

- [Orthogonality of martingale increments](integral-sub-mul-eq-zero.md)
- [Pythagorean identity for martingale increments](integral-sub-sq-eq.md): Pythagorean identity
- [Conditional variance theorem for martingales](cond-exp-sub-sq-eq.md): conditional form
