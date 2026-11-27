# Asymptotic expansion of sampling probabilities under strong selection

**Model.** The $d$-allele Wright–Fisher diffusion on the simplex $\Delta = \{\mathbf x \in [0,1]^d : \sum_i x_i = 1\}$ has generator

$$\mathcal L^{(\sigma)} = \frac12\sum_{i,j} x_i(\delta_{ij} - x_j)\,\partial_{ij} + \sum_i\Big[\frac\theta2\Big(\sum_j P_{ji}x_j - x_i\Big) + \frac{x_i}{2}\Big(\sigma_i - \sum_j\sigma_jx_j\Big)\Big]\partial_i,$$

with mutation rate $\theta$, mutation matrix $P$ and selection parameters $\sigma_i$. The mutation matrix $P$ is assumed irreducible, which guarantees that the diffusion has a unique stationary distribution (with a density). Consider the strong-selection regime $\sigma_1 = \sigma \to \infty$ with all other parameters fixed. For a type-count vector $\mathbf n = (n_1,\dots,n_d)$ with $\|\mathbf n\| = \sum_i n_i$, the sampling probability $q^{(\sigma)}(\mathbf n)$ is the probability that an ordered sample drawn from the stationary distribution has these type counts, $q^{(\sigma)}(\mathbf n) = E\big[\prod_i X_i^{n_i}\big]$ under stationarity.

**Diffusion limits.** On the time scale $t/\sigma$, $\mathbf X^{(\sigma)}$ converges to the deterministic logistic sweep of allele $1$. At stationarity the unfit frequencies are of order $1/\sigma$: $\mathbf X^{(\sigma)} \approx \mathbf e_1 + \sigma^{-1}\mathbf Z(\infty)$, where the coordinates $Z_i(\infty)$, $i \ge 2$, are independent $\mathrm{Gamma}(\theta P_{1i}, 1)$ variables (mutation from the fit allele balanced by selection against the mutants).

**Theorem.** Assume $\sigma_2 = \dots = \sigma_d = 0$ (only the fit allele is selected). For every $K \ge 0$,

$$q^{(\sigma)}(\mathbf n) = \frac{1}{\sigma^{\|\mathbf n\| - n_1}}\Big\{\sum_{k=0}^K \tilde q_k(\mathbf n)\,\sigma^{-k} + O(\sigma^{-K-1})\Big\},$$

with leading coefficient

$$\tilde q_0(\mathbf n) = \prod_{i=2}^d \frac{\Gamma(\theta P_{1i} + n_i)}{\Gamma(\theta P_{1i})}.$$

The coefficients are characterized by boundary conditions and recursions: $\tilde q_k(\mathbf e_1) = \mathbf 1_{\{k=0\}} - \mathbf 1_{\{k\ge1\}}\sum_{i\ge2}\tilde q_{k-1}(\mathbf e_i)$, analogous boundary conditions for single unfit alleles, and

$$\tilde q_k(\mathbf n + \mathbf e_1) + \mathbf 1_{\{k\ge1\}}\sum_{j=2}^d \tilde q_{k-1}(\mathbf n + \mathbf e_j) = \tilde q_k(\mathbf n),$$

so all $\tilde q_k$ can be computed recursively. The restriction $\sigma_2 = \dots = \sigma_d = 0$ matters only beyond the leading term: the source notes that the leading coefficient $\tilde q_0$ (the Gamma approximation) does not depend on $\sigma_2, \dots, \sigma_d$, whereas whether the higher coefficients do is open in general. Under parent-independent mutation ($P_{ij} = Q_j$) they have a closed form $\tilde q_k = \tilde q_0 r_k - \sum_{m<k} s_{k-m}\tilde q_m$. The series is asymptotic, not convergent.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../k-allele-wright-fisher-generator-on-the-simplex.md)

## Expansion

The leading term is the Gamma approximation: $E\big[\prod_{i\ge2}(\sigma^{-1}Z_i)^{n_i}\big] = \sigma^{-(\|\mathbf n\| - n_1)}\prod_{i\ge2}(\theta P_{1i})^{\overline{n_i}}$, with $x^{\overline m}$ the rising factorial, and $X_1^{n_1} \to 1$. The higher-order recursions come from substituting the expansion into the exact recursion that the sampling probabilities satisfy (from stationarity of the generator, or equivalently from the ancestral selection graph): each power of $1/\sigma$ trades a fit sampled lineage for an unfit one. Dually, the ancestral selection graph run at speed $\sigma$ has a limiting branching–coalescing structure in which the limiting Wright–Fisher logistic dynamics and the limiting graph satisfy an asymptotic duality relation.

## Sources

- Martina Favero and Paul A. Jenkins, "Sampling probabilities, diffusions, ancestral graphs, and duality under strong selection", *Electronic Journal of Probability* 30 (2025), 1–42, <https://doi.org/10.1214/25-ejp1302>. Numbering as in the preprint arXiv:2312.17406v3, <https://arxiv.org/abs/2312.17406v3>: Proposition 2.1 (diffusion limits), Proposition 4.1 (Gamma sampling), Theorem 4.4 (asymptotic coefficients), Corollary 4.5 (parent-independent mutation) and Proposition 4.6.
