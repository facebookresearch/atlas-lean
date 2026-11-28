# Small-mutation limits of stationary laws

Burden and Griffiths (2019, Section 2) consider the neutral $d$-allele Wright–Fisher diffusion with backward generator

$$\mathcal L = \frac12\sum_{i,j=1}^dx_i(\delta_{ij} - x_j)\frac{\partial^2}{\partial x_i\partial x_j} + \sum_{i,j=1}^d\gamma_{ji}x_j\frac{\partial}{\partial x_i}, \qquad \gamma_{ij} = \frac\theta2(P_{ij} - \delta_{ij}),$$

with total mutation rate $\theta/2$ and an irreducible mutation transition matrix $P$ with stationary distribution $\pi$ (their equation (1)), and write $p(\boldsymbol n; \theta)$ for the probability of the type configuration $\boldsymbol n$ of a sample of $n$ genes taken from the stationary distribution. Their Theorem 1 states that, as $\theta \to 0$, for each type $a$,

$$p(n\boldsymbol e_a; \theta) = \pi_a\Bigl(1 - \theta(1 - P_{aa})\sum_{l=1}^{n-1}\frac1l\Bigr) + O(\theta^2)$$

(their equation (7)). In particular, for every $n$ a stationary sample is, with probability tending to $\pi_a$, monomorphic of type $a$. The following consequence is derived here: since the sampling probabilities are the moments $\binom{n}{\boldsymbol n}E[X_1^{n_1}\cdots X_d^{n_d}]$ of the stationary law (their equation (2)), and these moments determine a law on the simplex, the stationary law converges weakly as $\theta \to 0$ to $\sum_a\pi_a\delta_{\boldsymbol e_a}$, the law that puts mass $\pi_a$ on the population fixed for type $a$. For two alleles this is the limit $p_0\,\delta_0 + p_1\,\delta_1$ of the stationary frequency of one type, with weights given by the stationary distribution $\pi$ of the $2 \times 2$ matrix $P$.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](k-allele-wright-fisher-generator-on-the-simplex.md)

## Expansion

1. The neutral $d$-allele diffusion (1), its stationary sampling probabilities (2) and their recursion.
2. The small-$\theta$ expansion of the monomorphic sampling probabilities, equation (7), by the coalescent argument with at most one mutation in the tree.
3. The weak limit $\sum_a\pi_a\delta_{\boldsymbol e_a}$ of the stationary law, from the convergence of all moments.
4. Not stated in the cited source, a separate target: with genic selection $\sigma$ and two alleles with mutation rates $\theta_1 = \varepsilon\alpha_1$, $\theta_2 = \varepsilon\alpha_2$, the weak limit $p_0\,\delta_0 + p_1\,\delta_1$ of the stationary law as $\varepsilon \to 0$ with $p_1/p_0 = (\alpha_1/\alpha_2)e^{2\sigma}$, and its identification with the stationary law of the two-state substitution chain with rates $\frac{\theta_1}{2}K(\sigma)$ and $\frac{\theta_2}{2}K(-\sigma)$, $K(\sigma) = 2\sigma/(1 - e^{-2\sigma})$.

## Sources

- C. J. Burden and R. C. Griffiths, The stationary distribution of a sample from the Wright–Fisher diffusion model with general small mutation rates, J. Math. Biol. 78 (2019), 1211–1224, Section 2, equations (1), (2) and (7), and Theorem 1 (numbering of arXiv:1802.07875v2; the theorem is numbered 2.1 in another arXiv version). <https://doi.org/10.1007/s00285-018-1306-y>
