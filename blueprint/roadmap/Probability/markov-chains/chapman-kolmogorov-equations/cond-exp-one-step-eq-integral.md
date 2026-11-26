# One-step Chapman–Kolmogorov equation for functions

Let $X = (X_n)_{n \in \mathbb{N}}$ be a [Markov chain](is-markov-chain.md) with state space $S$
with respect to a filtration $(\mathcal{F}_n)$, with Markov transition kernel $\kappa$, under a
probability measure $\mu$. Let $f : S \to \mathbb{R}$ be strongly measurable and bounded. Then
for every $k \in \mathbb{N}$,

$$\mathbb{E}_\mu[f(X_{k+1}) \mid \mathcal{F}_k](\omega) = \int_S f(y) \, \kappa(X_k(\omega), dy)$$

for $\mu$-almost every $\omega$.
