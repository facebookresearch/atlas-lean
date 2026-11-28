# Genetic distance between subpopulations as a hitting time of two random walks

**Model.** A metapopulation consists of $d$ subpopulations $E = \{1,\dots,d\}$ of sizes $n_i^\varepsilon = \lfloor N_i/\varepsilon\rfloor$. Each individual carries one chromosome of length $1$ with $l^\varepsilon \to \infty$ loci at i.i.d. uniform positions. Within each subpopulation, individuals follow a neutral Moran model with recombination at constant rate $\lambda$. Mutations occur at rate $b^{\gamma,\varepsilon} = \gamma\varepsilon\,b_\infty$ per individual per locus (infinitely many alleles), and at rate $m^\gamma_{ij} = \gamma M_{ij}$ one individual migrates from $i$ to $j$ and replaces a uniformly chosen resident. The genetic distance $\delta_t(x,y)$ between two individuals is the fraction of loci at which they differ, and the distance $d^{\gamma,\varepsilon}_t(i,j)$ between subpopulations is the modified Hausdorff distance

$$d^{\gamma,\varepsilon}_t(i,j) = \Big(\frac{1}{n_i^\varepsilon}\sum_{x\in i}\min_{y\in j}\delta_t(x,y)\Big) \vee \Big(\frac{1}{n_j^\varepsilon}\sum_{y\in j}\min_{x\in i}\delta_t(x,y)\Big).$$

**Theorem.** Let $S^i$ and $S^j$ be independent continuous-time random walks on $E$ started at $i$ and $j$, with jump rate $\tilde M_{kp} = M_{pk}/N_k$ from $k$ to $p$ (the backward migration rates), and let $\tau_{ij} = \inf\{t \ge 0 : S^i(t) = S^j(t)\}$. Define

$$D_t(i,j) = 1 - \int_0^t e^{-2b_\infty s}\,\mathbb{P}(\tau_{ij} \in ds) - e^{-2b_\infty t}\,\mathbb{P}(\tau_{ij} > t).$$

If the metapopulation is initially homogeneous (all individuals share one genotype), then, taking first the rare mutation–migration limit $\gamma \to 0$ and then the large population–dense loci limit $\varepsilon \to 0$,

$$\lim_{\varepsilon\to0}\lim_{\gamma\to0}\big(d^{\gamma,\varepsilon}_{t/(\gamma\varepsilon)}(i,j)\big)_{t\ge0} = \big(D_t(i,j)\big)_{t\ge0}$$

in the sense of finite-dimensional distributions; in particular

$$\lim_{t\to\infty} D_t(i,j) = 1 - \mathbb{E}\big(e^{-2b_\infty \tau_{ij}}\big).$$

So the asymptotic genetic distance depends on the whole migration graph through the meeting time of two backward lineages, not only on the direct migration rates between $i$ and $j$.

**Intermediate steps.** (i) As $\gamma \to 0$, subpopulations are homogeneous at almost every locus and the individual-based model converges to a population-based model in which a new mutation fixes in subpopulation $i$ at rate $b_\infty l^\varepsilon$ and a migration from $i$ to $j$ simultaneously fixes the migrant alleles on a random set $S$ of loci at rate $\varepsilon^{-1}M_{ij}\,\mathbb{P}(\mathcal{F}_j = S)$, where $\mathcal{F}_j$ is the set of migrant loci that fix in a Moran model with recombination. (ii) As $\varepsilon \to 0$, the empirical distribution of allelic partitions along the chromosome converges to the solution of the forward Kolmogorov equation of a single-locus partition process (an ergodic theorem along the chromosome), because recombination decorrelates distant loci.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

At one locus, the partition of $E$ by allelic identity is dual to a system of coalescing random walks run backward in time with the reversed migration rates $\tilde M$: two subpopulations carry the same allele at time $t$ if their lineages meet before either is hit by a mutation, and each lineage mutates at rate $b_\infty$ on the time scale $t/(\gamma\varepsilon)$, hence the factor $e^{-2b_\infty s}$ at meeting time $s$. Starting from a homogeneous population, lineages that have not met by time $t$ still share the ancestral allele unless a mutation hit them, giving the last term of $D_t$. The dense-loci limit turns the fraction of differing loci into the probability that one locus differs. If initial diversity is present with limiting partition law $P^0$, the last term is replaced by $\int e^{-2b_\infty t}\,\mathbb{P}(\tau_{ij} > t,\ S^i(t) \sim_\pi S^j(t))\,P^0(d\pi)$.

## Sources

- Verónica Miró Pina and Emmanuel Schertzer, "How does geographical distance translate into genetic distance?", *Stochastic Process. Appl.* 129(10) (2019), 3893–3921. <https://doi.org/10.1016/j.spa.2018.11.004>
- Preprint version (the locators in this item follow its numbering): Verónica Miró Pina and Emmanuel Schertzer, "How does geographical distance translate into genetic distance?", arXiv:1703.00357 (2017), Theorem 1.1 (Section 1), Definition 2.1 and Theorem 2.2 (Section 2), Theorem 3.1 (Section 3) and Theorem 5.1 (Section 5), <https://doi.org/10.48550/arXiv.1703.00357>.
