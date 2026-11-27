# Quartet concordance-factor pseudolikelihood of a phylogenetic network

Let $N$ be a semi-directed level-1 phylogenetic network on $n \ge 4$ taxa, with branch lengths $t$ in coalescent units and inheritance probabilities $\gamma$. Let $\mathcal G = \{G_1, \dots, G_g\}$ be gene trees from $g$ unlinked loci. For each four-taxon set $s$, with quartets $q_1(s), q_2(s), q_3(s)$, let $X_{q_i}(s)$ be the number of gene trees that display $q_i(s)$, and let $\mathrm{CF}_{q_i}(s; N, t, \gamma)$ be the [quartet concordance factors](quartet-concordance-factors-of-a-four-taxon-level-1-network.md) the network predicts.

For each fixed $s$, independence across loci makes $(X_{q_1}, X_{q_2}, X_{q_3})$ multinomial with probabilities $(\mathrm{CF}_{q_1}, \mathrm{CF}_{q_2}, \mathrm{CF}_{q_3})$. The **pseudolikelihood** multiplies these four-taxon likelihoods over all $\binom n4$ four-taxon sets $\mathcal S$, ignoring the dependence between overlapping sets:

$$\mathcal L(N, t, \gamma) = \prod_{s \in \mathcal S} \mathrm{CF}_{q_1}(s)^{X_{q_1}(s)}\, \mathrm{CF}_{q_2}(s)^{X_{q_2}(s)}\, \mathrm{CF}_{q_3}(s)^{X_{q_3}(s)} .$$

The maximum pseudolikelihood estimator maximizes $\mathcal L$ over topologies with $h$ reticulations and over $(t, \gamma)$. The data enter only through the quartet counts, which may be replaced by estimated concordance factors that account for gene-tree uncertainty.

**Detectability (generic, under $t \in (0, \infty)$ on tree edges and $\gamma \in (0,1)$).** Let $k$ be the number of nodes in a reticulation cycle.

- $k = 2$: the hybrid edge is not detectable, for any $n$.
- $k = 3$: detectable when at least two of the three subtrees cut off by the cycle contain more than one taxon. When the cycle induces a $(1,1,n-2)$ partition: not detectable if the hybrid node has a single descendant taxon (non-hybrid subtrees of sizes $1$ and $n-2$); if the hybrid node has the $n-2 \ge 2$ descendant taxa below it (both non-hybrid subtrees single taxa), detectable on some positive-measure parameter sets and not on others. Solís-Lemus and Ané state the $k = 3$ case as "if and only if"; the last case is the later correction of Allman et al. (2024), Proposition 6(2) and Theorem 19(1), stated in [topological identifiability of a level-1 species network from quartet CFs](level-1-topological-identifiability-from-quartet-cfs.md), item 1.
- $k \ge 4$ and $n \ge 5$: detectable, and with $n \ge 5$ the direction of the hybrid edge, which four taxa cannot resolve, becomes identifiable in the case studied.
- For a fixed topology with $n \ge 5$: $(t, \gamma)$ is identifiable if $k \ge 5$ and not if $k \le 3$. For $k = 4$ it is identifiable in the "good diamond" configurations; in the two "bad diamond" cases some parameters must be reparametrized or fixed.

Because quartet CFs are root-independent, only the semi-directed network can be estimated, never the root.

## Depends on

- [Quartet concordance factors of a four-taxon level-1 network](quartet-concordance-factors-of-a-four-taxon-level-1-network.md)

## Expansion

Each factor is an honest multinomial likelihood for one four-taxon subnetwork. The product is a composite likelihood, so the four-taxon formulas suffice and no full network gene-tree likelihood is needed. The detectability results compare the polynomial systems of $3\binom n4$ CFs for a network $N$ and for $N'$, the network with one hybrid edge removed. They were checked by algebraic elimination, and the equal-CF solutions were found only on the excluded boundary $t_b \in \{0, \infty\}$ or $\gamma = 0$. The search over networks is restricted to identifiable configurations. For the "bad diamond I" case the three non-identifiable parameters $(\gamma, t_1, t_0)$ are reparametrized as the two identifiable combinations $\gamma(1 - e^{-t_0})$ and $(1-\gamma)(1 - e^{-t_1})$.

## Sources

- C. Solís-Lemus and C. Ané, "Inferring phylogenetic networks with maximum pseudolikelihood under incomplete lineage sorting", *PLoS Genetics* 12(3) (2016), e1005896, <https://doi.org/10.1371/journal.pgen.1005896> (PMC4780787), Equation (1) and the Models section ("Pseudolikelihood on a network", "Detecting the presence of a hybridization", "Identifiability of branch lengths and heritabilities", "Practical consequences"; Figures 4–5).
- E. S. Allman, H. Baños, M. Garrote-López and J. A. Rhodes, "Identifiability of level-1 species networks from gene tree quartets", *Bulletin of Mathematical Biology* 86 (2024), 110, <https://doi.org/10.1007/s11538-024-01339-4> (PMC11272829), Proposition 6(2) and Theorem 19(1).
