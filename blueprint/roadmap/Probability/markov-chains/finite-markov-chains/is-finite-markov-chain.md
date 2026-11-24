# Finite-state Markov chain with a given transition matrix

Let $\mu$ be a measure on a measurable space $\Omega$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be
a filtration, and let $P$ be a [stochastic
matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md) on the states
$\{0, 1, \dots, M\}$. A sequence of maps $X_n : \Omega \to \{0, 1, \dots, M\}$ is a finite-state
Markov chain with transition matrix $P$ with respect to $(\mathcal{F}_n)$ under $\mu$ if

1. each $X_n$ is $\mathcal{F}_n$-measurable, and
2. for every $n \in \mathbb{N}$ and every state $j$,

    $$\mathbb{E}_\mu[\mathbf{1}_{\{X_{n+1} = j\}} \mid \mathcal{F}_n] = P(X_n, j)$$

    $\mu$-almost everywhere.

For a probability measure $\mu$, condition 2 is the Markov property
$P(X_{n+1} = j \mid \mathcal{F}_n) = P_{X_n j}$.
