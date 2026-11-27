# The multispecies coalescent as a constructed process

Let $S$ be a well-labelled rooted species tree with nonnegative branch lengths and an infinite root population, as in [the multispecies coalescent](gene-tree-prob.md). Construct a gene genealogy by running independent Kingman coalescents on the branches of $S$, from the leaves to the root: the lineages that leave a branch at its top vertex enter the ancestral population together with those of the sibling branch, and on each branch the lineages coalesce as in [the realized coalescent on one branch](one-species-tree-branch-exit-law-and-merge-order.md).

The law of the cluster set of the resulting gene tree equals the gene tree probability of [the multispecies coalescent](gene-tree-prob.md).

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)
- [One species-tree branch: exit law and merge order from the realized coalescent](one-species-tree-branch-exit-law-and-merge-order.md)

## Expansion

1. The construction as a measurable map from independent per-branch coalescents to gene trees.
2. The equality of laws, by induction over the branches of $S$ from the leaves.
3. Checks: the three-species gene tree probabilities are recovered, and in the root population the lineages coalesce to one almost surely.

## Sources

- J. H. Degnan and L. A. Salter, Gene tree distributions under the coalescent process, *Evolution* 59 (2005), 24–37 (gene tree distributions).
- B. Rannala and Z. Yang, Bayes estimation of species divergence times and ancestral population sizes using DNA sequences from multiple loci, *Genetics* 164 (2003), 1645–1656, <https://pubmed.ncbi.nlm.nih.gov/12930768/> (the multispecies coalescent).
