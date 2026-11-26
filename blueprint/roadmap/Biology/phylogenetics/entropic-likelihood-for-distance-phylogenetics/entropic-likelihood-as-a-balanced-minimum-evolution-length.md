# Entropic likelihood as a balanced-minimum-evolution tree length

**Setting.** Sites evolve independently along an unrooted binary topology $\mathcal{U}$ with branch lengths $\boldsymbol b = (b_i)$ under a reversible continuous-time Markov chain with stationary law $\pi$ and transition probabilities $P_{ab}(t)$. For a site pattern $G$ on all nodes, $p(G,\mathcal U,\boldsymbol b) = \pi_{z_r}\prod_i P_{z^1_i z^2_i}(b_i)$, independent of the choice of root $r$ by reversibility. Let
$$S(t) = -\mathbb{E}\big[\log P_{M_0 M_t}(t)\big]$$
be the entropy of the mutation chain run for time $t$ from stationarity ($M$ a copy of the chain with $M_0 \sim \pi$).

**Proposition (expected log-likelihood).** Since each branch's endpoint states are distributed as $(M_0, M_{b_i})$,
$$\mathbb{E}\big[\log p(G, \mathcal U, \boldsymbol b)\big] = \text{const} - \sum_i S(b_i),$$
so for $N$ sites the expected log-likelihood is $-N$ times the length of the tree whose branch $i$ has length $S(b_i)$, up to a topology-independent constant.

**Definition (entropic likelihood).** Let $d^S_{ij}$ be the path distance between taxa $i, j$ in this entropy-weighted tree and $e_{ij}$ the number of edges between them in $\mathcal U$. By Pauplin's formula for the balanced minimum evolution (BME) length,
$$\ell_S(\mathcal U) = -N\sum_{i \ne j} 2^{-e_{ij}}\,d^S_{ij},$$
the sum running over ordered pairs. $\ell_S$ depends on the data only through pairwise distances, so it can be evaluated in $O(n^2)$ per topology and used as a generalized-Bayes likelihood in tree MCMC.

**Theorem (linear relation to the BME objective).** Let $K = \sum_{a\ne b}\pi_aQ_{ab}$ be the total substitution rate. In the regime $K t \to 0$ with $\pi$ and rate ratios fixed, under a tree-generating prior with exponential branch lengths of rate $\theta$, the expected entropic distance between taxa a tree distance $t$ apart is affine in $t$ up to relative error $O\big(1/\log(K/\theta)\big)$: the slope is $\int_0^\infty S(s)\,\theta^2 e^{-\theta s}\,ds$. Hence $\ell_S$ is, to that order, an affine function of the classical BME objective, which explains why distance methods and Felsenstein likelihood rank topologies similarly.

## Depends on

- [Pauplin's formula](../pauplin-s-formula-and-balanced-minimum-evolution/bme-length-path-length.md)

## Expansion

Taking expectations of the log of the product of transition probabilities gives one entropy term per branch. Summing branch quantities over a tree is exactly what Pauplin's formula computes from leaf-to-leaf distances with weights $2^{-e_{ij}}$, so the expected log-likelihood becomes a BME length of an entropy-transformed distance matrix. For short total divergence, $S(t) \approx Kt\log(1/(Kt))$ near $0$, which grows almost linearly on the scale of typical branch lengths; integrating against the exponential branch-length prior and integrating by parts twice bounds the nonlinear remainder by a factor $1/\log(K/\theta)$.

## Sources

- M. J. Penn, N. Scheidwasser, M. P. Khurana, C. A. Donnelly, D. A. Duchêne and S. Bhatt, "Generalised Bayesian distance-based phylogenetics for the genomics era", arXiv:2502.04067 (2025), Methods (derivation of the entropic likelihood, Equations for $\ell(\mathcal U)$ and $\ell_S(\mathcal U)$) and the supplementary theorem on the linear BME approximation, <https://doi.org/10.48550/arXiv.2502.04067>.
