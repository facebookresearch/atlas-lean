# Statistical consistency of NJMerge divide-and-conquer pipelines

**Pipeline.** Given data on a species (or sequence) set $S$: (1) compute a distance matrix $D$ with a method $M_D$; (2) split $S$ into $k$ pairwise disjoint subsets (for instance by decomposing a neighbor-joining tree on $D$ into subsets of bounded size); (3) estimate a tree on each subset with a method $M_T$, giving constraint trees $\mathcal T$; (4) run [NJMerge](njmerge-returns-the-true-tree-on-nearly-additive-input.md) on $(\mathcal T, D)$.

**Consistency.** Under a model tree $(T, \Theta)$, a tree estimator is statistically consistent if for every $\epsilon > 0$ there is a data size (sequence length $l$ under the GTR model; number $m$ of true gene trees under the multispecies coalescent, MSC) beyond which it returns $T$ with probability at least $1 - \epsilon$.

**Corollary 5 (gene trees).** Suppose the pipeline produces $k$ subsets, neighbor joining on distances from $M_D$ is statistically consistent under the GTR model (for example with log-det distances), and $M_T$ is statistically consistent under GTR (for example maximum likelihood). Then the pipeline is statistically consistent under the GTR model.

**Corollary 7 (species trees).** Suppose the pipeline produces $k$ subsets, neighbor joining on distances from $M_D$ is statistically consistent under the MSC (for example the average gene-tree internode distance matrix, which converges to an additive matrix for the species tree), and $M_T$ is statistically consistent under the MSC (for example ASTRAL). Then the pipeline is statistically consistent under the MSC.

## Depends on

- [NJMerge returns the true tree on nearly additive input](njmerge-returns-the-true-tree-on-nearly-additive-input.md)
- [The multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)

## Expansion

Fix $\epsilon$ and choose $\epsilon_D, \epsilon_T > 0$ with $\epsilon_D + k\epsilon_T < \epsilon$. For enough data, neighbor joining on $D$ returns $T^*$ with probability at least $1 - \epsilon_D$, and each of the $k$ subset trees agrees with $T^*$ with probability at least $1 - \epsilon_T$. These events are dependent (they come from the same data, and the subsets are chosen from $D$), but the union bound gives probability at least $1 - \epsilon_D - k\epsilon_T > 1 - \epsilon$ that all of them hold. On that event NJMerge returns $T^*$, by the form of Theorem 3 its proof establishes: NJMerge reproduces neighbor joining whenever neighbor joining returns $T^*$ and every constraint tree agrees with $T^*$. (The source multiplies the probabilities as if the events were independent.) In simulations with 100 and 1000 taxa NJMerge failed to return a tree in under 1% of runs and let SVDquartets and concatenated maximum likelihood finish on 1000-taxon, 1000-gene data sets within 64 GB of memory.

## Sources

- E. K. Molloy and T. Warnow, "Statistically consistent divide-and-conquer pipelines for phylogeny estimation using NJMerge", Algorithms for Molecular Biology 14 (2019) 14, Definitions 4 and 6, Corollaries 5 and 7, <https://doi.org/10.1186/s13015-019-0151-x>, PMCID PMC6642500.
