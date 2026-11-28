# Relabeling invariance of Kingman's n-coalescent

Let Kingman's $n$-coalescent act on the labelled sample $\{1, \dots, n\}$. For a permutation $\sigma$ of the labels, the $n$-coalescent is invariant in law under relabelling by $\sigma$: every pair of blocks merges at rate $1$ whatever their labels, so the generator commutes with the action of $\sigma$ on partitions. Berestycki (2009, Section 2.1.1) uses exactly this invariance of the $n$-coalescent under permutations of $\{1, \dots, n\}$ to conclude that Kingman's coalescent on $\mathbb N$ is exchangeable at every time $t > 0$, although its standard construction from pairwise exponential clocks favours lower labels.

## Depends on

- [Exchangeability of the jump chain](../../../Biology/coalescent-theory/partition-valued-kingman-coalescent/jump-law-comap-perm.md)
- [Exchangeability of the time-t marginal](../../../Biology/coalescent-theory/partition-valued-kingman-coalescent/time-law-comap-perm.md)
- [Kingman's formula is invariant under relabeling](../../../Biology/coalescent-theory/partition-valued-kingman-coalescent/kingman-prob-comap-perm.md)

## Expansion

1. The action of permutations on sample partitions, on partition-valued paths and on branch-indexed point configurations.
2. Invariance of the joint law of the jump chain and the holding times, from the invariance of the rates under relabelling.
3. Separate target, not stated by Berestycki: relabeling invariance of the marked genealogy, the partition-valued path together with, under the infinite-sites model, the Poisson mutations placed on its branches (the [marked Kingman model](../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-measure.md)). The holding times depend on the path only through the numbers of blocks, which relabelling does not change, and given the genealogy the mutations form a Poisson process on its branches with intensity proportional to branch length, which relabelling carries to the Poisson process on the relabelled branches.
4. Separate target, not stated by Berestycki, from item 3: every statistic that is a symmetric function of the sample, such as the site-frequency spectrum, the number of segregating sites or the mean number of pairwise differences, has the same law before and after relabelling; and an example of a statistic that is not symmetric (the number of differences between two fixed labels) whose law is nevertheless invariant by the same argument.

## Sources

- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009, Section 2.1.1. <https://arxiv.org/abs/0909.3985>
