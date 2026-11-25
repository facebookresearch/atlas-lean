# Finite-state Markov chains satisfy the general one-step Markov property

Let $\mu$ be a probability measure on $\Omega$, $(\mathcal{F}_n)_{n \in \mathbb{N}}$ a
filtration, $P$ a [stochastic matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)
on the states $S = \{0, 1, \dots, M\}$ with [transition kernel](finite-chain-kernel.md)
$\kappa_P$, and $X = (X_n)$ a [finite-state Markov chain](is-finite-markov-chain.md) with
transition matrix $P$ with respect to $(\mathcal{F}_n)$ under $\mu$. Then for every $n \in
\mathbb{N}$ and every subset $B \subseteq S$,

$$\mathbb{E}_\mu[\mathbf{1}_B(X_{n+1}) \mid \mathcal{F}_n] = \kappa_P(X_n, B) = \sum_{j \in B} P(X_n, j)$$

$\mu$-almost everywhere. No measurability condition on $B$ is needed, since $S$ is finite.
