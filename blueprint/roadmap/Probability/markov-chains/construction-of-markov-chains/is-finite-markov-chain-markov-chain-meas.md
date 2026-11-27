# Canonical Markov law satisfies the finite Markov chain specification

Let $P$ be a [stochastic matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)
on the states $\{0, 1, \dots, M\}$, with [transition
kernel](../finite-markov-chains/finite-chain-kernel.md) $\kappa_P$, and let $i$ be a state. On
the path space $\{0, \dots, M\}^{\mathbb{N}}$, let $X_n(\omega) = \omega_n$ be the coordinate
process, let $\mathcal{F}_n = \sigma(X_0, \dots, X_n)$ be its natural filtration, and let
$P_{\delta_i}$ be the [canonical Markov chain measure](markov-chain-measure.md) with initial
distribution $\delta_i$ and transition kernel $\kappa_P$. Then $(X_n)$ is a [finite-state Markov
chain](../finite-markov-chains/is-finite-markov-chain.md) with transition matrix $P$ with respect
to $(\mathcal{F}_n)$ under $P_{\delta_i}$.
