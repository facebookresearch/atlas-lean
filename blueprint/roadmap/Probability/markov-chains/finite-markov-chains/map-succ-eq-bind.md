# One-step forward equation

Let $X = (X_n)$ be a [finite-state Markov chain](is-finite-markov-chain.md) with transition
matrix $P$ with respect to a filtration, under a probability measure $\mu$, and let $\kappa_P$ be
the [transition kernel](finite-chain-kernel.md) of $P$. Then for every $n \in \mathbb{N}$ the law
of $X_{n+1}$ is the law $\nu_n$ of $X_n$ transported by $\kappa_P$:

$$\mu(X_{n+1} \in B) = \int \kappa_P(x, B) \, d\nu_n(x) = \sum_x \mu(X_n = x)\, \kappa_P(x, B)$$

for every set of states $B$.
