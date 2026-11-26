# Fixation probability of a beneficial allele under Beta-coalescent reproduction

**Model.** A two-type population of fixed size $N$ (wild type and an advantageous type) reproduces by neutral skewed-offspring events in the domain of attraction of the $\Lambda$-Wright–Fisher diffusion with $\Lambda = \mathrm{Beta}(2-\alpha, \alpha)$, $\alpha \in (1,2)$: at a neutral event a single individual replaces a random fraction of the population, so a whole fraction can descend from one parent. In addition the advantageous type has selective reproduction events with strength $s_N = N^{-b}$ (moderate selection), $0 < b < \alpha - 1$. Let $\pi_N$ be the probability that a single advantageous mutant eventually fixes.

**Theorem.**
1. As $N \to \infty$,

$$\pi_N \sim \alpha^{\frac{1}{\alpha-1}}N^{-\frac{b}{\alpha-1}} = \big(\alpha s_N\big)^{\frac{1}{\alpha-1}}.$$

2. *(Duality.)* The number $X^{(N)}_t$ of advantageous individuals is in hypergeometric duality with the block-counting process $A^{(N)}$ of a $\Lambda$-ancestral selection graph:

$$\mathbb E\Big[\tfrac{(X_t)_n}{(N)_n}\,\Big|\, X_0 = k\Big] = \mathbb E\Big[\tfrac{(k)_{A_t}}{(N)_{A_t}}\,\Big|\, A_0 = n\Big], \qquad (m)_j = m(m-1)\cdots(m-j+1),$$

and consequently $\pi_N = \mathbb E[A^{(N)}_{\mathrm{eq}}]/N$, where $A^{(N)}_{\mathrm{eq}}$ has the stationary law of $A^{(N)}$.

## Expansion

Under Kingman-type reproduction (Haldane's formula) the fixation probability is of order $s_N$; heavy-tailed offspring change this to $s_N^{1/(\alpha-1)}$, which is much smaller because a single mutant must survive multiple-merger resampling events that wipe out large fractions. In the dual, the ancestral selection graph branches at rate about $s_N$ per lineage (selective arrows) and coalesces in Beta$(2-\alpha,\alpha)$ fashion, at total rate of order $n^\alpha$ with $n$ lineages. Branching grows linearly in the number of lineages while multiple mergers remove lineages superlinearly, so the stationary number of lineages is set by balancing the two, which produces the exponent $1/(\alpha-1)$ and the prefactor $\alpha^{1/(\alpha-1)}$. The proof makes this rigorous with Lyapunov-type test functions bounding $\mathbb E[A_{\mathrm{eq}}]$ from above and below.

## Sources

- M. Birkner, F. Boenkost, I. Dahmer, C. Pokalyuk, "On the fixation probability of an advantageous allele in a population with skewed offspring distribution", arXiv:2310.09045 (2023), Theorem 1, Proposition 1.3 and Corollary 1.4, <https://doi.org/10.48550/arXiv.2310.09045>.
