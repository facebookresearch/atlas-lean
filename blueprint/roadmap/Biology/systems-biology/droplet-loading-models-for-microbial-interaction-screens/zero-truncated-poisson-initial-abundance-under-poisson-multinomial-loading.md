# Zero-truncated Poisson law of a species' initial abundance under Poisson–multinomial loading

**Model.** A droplet is seeded from a pooled culture of $S$ species with relative frequencies $p_1, \dots, p_S$ ($\sum_s p_s = 1$). The total number of cells in the droplet is Poisson with mean $\lambda$, and given the total, the species labels are multinomial with probabilities $(p_s)$. Let $N_s(0)$ be the initial abundance of species $s$ and $O = \operatorname{supp}(N(0)) = \{s : N_s(0) > 0\}$ the set of species observed in the droplet.

**Theorem.** For any two subsets $\Omega_1, \Omega_2 \subseteq [S]$ with $s \in \Omega_1 \cap \Omega_2$ and every $n \ge 1$,

$$\mathbb P\bigl(N_s(0) = n \mid O = \Omega_1\bigr) = \frac{(p_s \lambda)^n / n!}{e^{p_s \lambda} - 1} = \mathbb P\bigl(N_s(0) = n \mid O = \Omega_2\bigr),$$

and consequently, for every measurable $\phi : \mathbb N \to \mathbb R$ with finite expectation,

$$\mathbb E\bigl[\phi(N_s(0)) \mid O = \Omega_1\bigr] = \frac{\sum_{n \ge 1} \phi(n)\, (p_s \lambda)^n / n!}{e^{p_s \lambda} - 1} = \mathbb E\bigl[\phi(N_s(0)) \mid O = \Omega_2\bigr].$$

Thus, once a species is known to be present, its starting abundance is zero-truncated Poisson with mean parameter $p_s \lambda$, irrespective of which other species share the droplet.

## Expansion

By Poisson thinning, a Poisson($\lambda$) total split multinomially gives independent counts $N_s(0) \sim \mathrm{Poisson}(p_s \lambda)$. The event $\{O = \Omega\}$ is the intersection of $\{N_s(0) > 0\}$ for $s \in \Omega$ and $\{N_t(0) = 0\}$ for $t \notin \Omega$, so by independence conditioning on it only truncates the law of $N_s(0)$ at zero. This invariance is what lets droplets with different co-occurring species be pooled when estimating the effect of a partner on the growth of $s$; working models that relax Poisson loading or sampling with replacement (negative-binomial or Dirichlet-multinomial loading) break it and induce dependence between co-loaded species.

## Sources

- W. Krinsman, "Statistics of High-Throughput Characterization of Microbial Interactions", PhD dissertation, arXiv:2210.09080 (2022), Corollaries 1 and 2, <https://doi.org/10.48550/arXiv.2210.09080>.
