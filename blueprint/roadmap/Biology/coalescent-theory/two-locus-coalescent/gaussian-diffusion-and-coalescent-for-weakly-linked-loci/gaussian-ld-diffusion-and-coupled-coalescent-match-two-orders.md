# Gaussian linkage-disequilibrium diffusion and coupled coalescent for weakly linked loci

**Setting.** Two neutral loci A and B with $K$ and $L$ alleles mutate (rates $\theta_A,\theta_B$, transition matrices $P^A,P^B$) and recombine at scaled rate $\rho$. A sample has $\mathbf a$ haplotypes typed only at A, $\mathbf b$ typed only at B and $\mathbf c=(c_{ij})$ typed at both, with $c=\sum c_{ij}$ and marginal counts $\mathbf c_A,\mathbf c_B$. Let $q(\mathbf a,\mathbf b,\mathbf c)$ be its sampling probability under the two-locus Wright–Fisher diffusion (equivalently the ancestral recombination graph), and $q^A,q^B$ the one-locus sampling distributions. For large $\rho$,

$$q=q_0+\frac{q_1}{\rho}+O(\rho^{-2}),\qquad q_0(\mathbf a,\mathbf b,\mathbf c)=q^A(\mathbf a+\mathbf c_A)\,q^B(\mathbf b+\mathbf c_B),$$

$$q_1=\binom c2q^Aq^B-q^B\sum_i\binom{c_{i\cdot}}2q^A(\cdot-\mathbf e_i)-q^A\sum_j\binom{c_{\cdot j}}2q^B(\cdot-\mathbf e_j)+\sum_{i,j}\binom{c_{ij}}2q^A(\cdot-\mathbf e_i)\,q^B(\cdot-\mathbf e_j),$$

with arguments $\mathbf a+\mathbf c_A$ and $\mathbf b+\mathbf c_B$ (the Jenkins–Song expansion).

**Gaussian diffusion model.** In a Moran model with recombination rate $\rho_\beta=\rho N^{\beta-1}$ that is large on the coalescent time scale, the allele frequencies $\mathbf X,\mathbf Y$ at the two loci change slowly while the linkage disequilibria $D_{ij}=\text{(haplotype frequency)}-X_iY_j$ relax quickly; a central limit theorem for density-dependent processes shows that, given $\mathbf X,\mathbf Y$, the vector $\mathbf D$ behaves like an Ornstein–Uhlenbeck process damped toward $0$ at rate $\rho_\beta/2$, with stationary law $\mathrm{Normal}(\mathbf 0,\boldsymbol\sigma_\infty/\rho)$, where

$$[\boldsymbol\sigma_\infty]_{ij,kl}=X_iY_j(\delta_{ik}-X_k)(\delta_{jl}-Y_l).$$

Take $\mathbf X\sim\pi_A$ and $\mathbf Y\sim\pi_B$ independent (one-locus stationary laws) and $\mathbf D$ conditionally Gaussian as above.

**Theorem.**

1. Under this Gaussian model the sampling distribution $q_G(\mathbf a,\mathbf b,\mathbf c)$ is available in closed form: it is a finite sum over $\lambda=0,\dots,\lfloor c/2\rfloor$ of $\rho^{-\lambda}$ times signed combinations of products $q^A(\cdot)\,q^B(\cdot)$ obtained from Gaussian moment (Wick pairing) formulas, and $q_G=q_0+q_1/\rho+O(\rho^{-2})$ with the same $q_0,q_1$ as the full model.
2. A simplified genealogical process $\mathcal D^{(\infty)}$, obtained by letting $\rho\to\infty$ in the two-locus ancestral process (fully linked lineages split into independent half-lineages that coalesce separately at each locus) and coupling it with the ancestral recombination graph through an auxiliary recombination process at rate $\rho c/2$, yields a sampling distribution whose first two terms in $1/\rho$ are again $q_0$ and $q_1$.

Both simpler models therefore capture the leading behavior of multilocus sampling probabilities under weak linkage, while the full models have no closed-form sampling distribution.

## Depends on

- [Two-locus coalescent](../README.md)

## Expansion

The Gaussian sampling formula follows by writing the probability of a sample as an expectation of products of haplotype frequencies $X_iY_j+D_{ij}$, expanding the products, and using that, conditionally on $\mathbf X,\mathbf Y$, odd moments of $\mathbf D$ vanish and even moments are sums over pairings of covariances $[\boldsymbol\sigma_\infty]/\rho$; each pairing contributes a factor $\rho^{-1}$ and polynomial moments of $\mathbf X$ and $\mathbf Y$, which are one-locus sampling probabilities. Truncating at $\lambda\le1$ recovers $q_0$ and $q_1$. For the coalescent, in the two-locus ancestral process a fully linked lineage recombines at rate $\rho c/2$, much faster than coalescence when $\rho$ is large; the coupling with $\mathcal D^{(\infty)}$ (Lemmas 4.1–4.3: the case $c=0$, the coupling itself, and a skeleton-chain representation) shows that the two processes differ only on events whose total contribution to the sampling probability is of order $\rho^{-2}$, so the expansions agree through order $\rho^{-1}$.

## Sources

- Paul A. Jenkins, Paul Fearnhead, Yun S. Song, "Tractable diffusion and coalescent processes for weakly correlated loci", *Electronic Journal of Probability* 20 (2015), <https://doi.org/10.1214/EJP.v20-3564>; preprint arXiv:1405.6863, <https://doi.org/10.48550/arXiv.1405.6863>. Numbering of the arXiv version: Section 2 (Theorem 2.1, after Jenkins and Song), Section 3 (Proposition 3.1, Theorem 3.1 after Norman, Theorem 3.2), Section 4 (Definitions 4.1 and 4.2, Lemmas 4.1–4.3, Theorem 4.1).
