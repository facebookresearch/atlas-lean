# Gene trees restricted to a taxon subset follow the induced species tree

Let $\sigma^+$ be a rooted metric species tree on a taxon set $X$, with internal edge lengths in coalescent units, and consider the multispecies coalescent with one lineage sampled per taxon. Allman, Degnan and Rhodes (2011, Lemma 5) show that for every subset $S \subseteq X$ the distribution of the gene tree restricted to $S$ is the multispecies coalescent distribution of the species tree $\sigma^+(S)$ induced on $S$: summing the gene tree probabilities on $X$ over all gene trees whose restriction to $S$ is a given tree gives that tree's probability on $\sigma^+(S)$, where an edge of $\sigma^+(S)$ has as length the sum of the lengths of the edges of $\sigma^+$ that it replaces. For four-taxon subsets, the resulting quartet concordance factors $\bigl(1 - \frac23 e^{-t}, \frac13 e^{-t}, \frac13 e^{-t}\bigr)$, with $t$ the internal edge length of the induced unrooted quartet, are stated in [quartet concordance factors depend only on the unrooted quartet network](../../multispecies-coalescent/quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md).

## Depends on

- [The multispecies coalescent](../../multispecies-coalescent/gene-tree-prob.md)

## Expansion

1. Restriction of a rooted metric species tree to a subset of taxa, with the lengths of merged edges added.
2. The marginalization identity of Lemma 5, from the description of the multispecies coalescent population by population.

## Sources

- E. S. Allman, J. H. Degnan and J. A. Rhodes, Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent, J. Math. Biol. 62 (2011; online 2010), 833–862, Lemma 5. <https://doi.org/10.1007/s00285-010-0355-7>
