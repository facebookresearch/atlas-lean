# Data requirement of concatenated distances and METAL under the multispecies coalescent

**Model.** A rooted binary species tree $S$ on $n$ leaves (species) $L$ has branch lengths $\tau_e > 0$ in coalescent units and per-branch mutation rates $\mu_e$; let $f = \min_e\tau_e$ (shortest branch), $\Delta = \max_{A,B}\tau_{AB}$ (diameter), $\mu_L = \min_e\mu_e$, $\mu_U = \max_e\mu_e$. Each of $m$ independent genes has a gene tree drawn from the multispecies coalescent on $S$ (one lineage per species); a gene-tree edge overlapping species edges $e$ for lengths $\sigma_{e\cap\tilde e}$ gets effective length $\delta_{\tilde e} = \sum_e\mu_e\sigma_{e\cap\tilde e}$, and $k$ sites per gene evolve independently along the gene tree under the Jukes–Cantor model, so two leaves at effective distance $\delta$ differ at a site with probability $\tfrac34(1 - e^{-4\delta/3})$. Write $\chi^{ij}_A$ for the state of species $A$ at site $j$ of gene $i$ and

$$\hat p_{AB} = \frac{1}{mk}\sum_{i\le m,\ j\le k}\mathbf 1\{\chi^{ij}_A \ne \chi^{ij}_B\}, \qquad \hat d_{AB} = -\tfrac34\log\big(1 - \tfrac43\hat p_{AB}\big).$$

**Theorem.**

1. (Molecular clock: concatenation is ultrametric.) If $\mu_e \equiv \mu$ and population sizes are constant, $\{\mathbb E[\hat p_{AB}]\}$ is an ultrametric on $L$ compatible with $S$: for every triple with topology $((A,B),C)$ in $S$,

$$\mathbb E[\hat p_{AC}] = \mathbb E[\hat p_{BC}] > \mathbb E[\hat p_{AB}] + \frac{3e^{-\frac43\mu\tau_{AC}}\,\mu}{8\mu+3}\,f.$$

Hence UPGMA applied to $\hat p$ returns $S$ with probability at least $1-\epsilon$ whenever $k \ge 1$ and

$$m \ge \frac{16\,e^{\frac83\mu\Delta}(8\mu+3)^2}{9\mu^2}\log\Big(\frac{8\binom n3}{\epsilon}\Big)\,f^{-2}.$$

2. (No clock: METAL.) In general, $d_{AB} = -\tfrac34\log(1 - \tfrac43\mathbb E[\hat p_{AB}])$ is an additive metric for $S$ with a quartet gap: if $((A,B),(C,D))$ or $(((A,B),C),D)$ holds in $S$, then

$$d_{AC} + d_{BD} = d_{AD} + d_{BC} > d_{AB} + d_{CD} + \alpha_{\mathrm{add}}, \qquad \alpha_{\mathrm{add}} = \tfrac34\log\big(\tfrac83\mu_L(1 - e^{-f}) + 1\big).$$

METAL, a quartet-based distance method (e.g. neighbor joining) run on $\hat d$, recovers the unrooted $S$ with probability at least $1-\epsilon$ whenever $k\ge1$ and

$$m \ge \frac{e^{\frac{8\mu_U\Delta}{3}}(8\mu_U+3)^2(24+8\alpha_{\mathrm{add}})^2}{162\,\alpha_{\mathrm{add}}^2}\log\Big(\frac{16\binom n4}{\epsilon}\Big),$$

a bound that behaves like a constant times $f^{-2}$ as $f\to0$. So a total of $mk = O(f^{-2})$ sites, even one site per gene, suffices.

## Depends on

- [The multispecies coalescent](../../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)
- [Closed form of the Jukes–Cantor difference probability](../../../jukes-cantor-model/p-diff-eq.md)
- [Jukes–Cantor distance](../../../jukes-cantor-model/jc-distance.md)
- [Ultrametric on taxa](../../../splits-compatibility-ultrametrics-and-upgma/is-ultrametric.md)
- [UPGMA is exact on ultrametrics](../../../splits-compatibility-ultrametrics-and-upgma/upgma-exact.md)

## Expansion

$\mathbb E[\hat p_{AB}] = \mathbb E[\tfrac34(1 - e^{-4\delta_{AB}/3})]$ averages over the random gene-tree distance $\delta_{AB}$, whose law under the coalescent depends only on the species-tree path from $A$ to their most recent common ancestral population and above. For $((A,B),C)$, pairs $(A,C)$ and $(B,C)$ have the same law, and the $(A,B)$ pair has an extra chance (of order $f$) to coalesce in their common ancestral branch, giving the gap. Hoeffding's inequality applied to the $mk$ indicator variables, with a union bound over the $\binom n3$ triples (or $\binom n4$ quartets), turns the gap into the sample bound. In the non-clock case the Jukes–Cantor correction is concave, so $d$ is not the expected gene-tree distance but still satisfies the four-point condition with a gap proportional to the minimal mutation rate times $1 - e^{-f}$.

## Sources

- Gautam Dasarathy, Robert Nowak, Sebastien Roch, "Data requirement for phylogenetic inference from multiple loci: a new distance method", arXiv (2014). Section 2 (species tree, multispecies coalescent, observation model), Theorems 1–4. <https://doi.org/10.48550/arXiv.1404.7055>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 12(2) (2015), 422–432, <https://doi.org/10.1109/tcbb.2014.2361685>; locators above refer to the arXiv version.
