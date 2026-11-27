# Consistency of exact quartet-support maximization for the unrooted species tree

Let $S$ be an unrooted binary species tree on a finite taxon set $X$ with $|X|\ge4$, all internal branch lengths positive in coalescent units, and let $G_1,G_2,\dots$ be independent gene trees, each the true (not estimated) unrooted topology of a locus drawn from the multispecies coalescent on $S$ with one lineage per taxon. For each four-taxon set $q$ with induced internal length $t_q>0$, the resolution $\rho_q$ induced by $S$ has probability $1-\frac23e^{-t_q}$ and each of the other two resolutions has probability $\frac13e^{-t_q}$, so $\rho_q$ is the strict plurality. Let $f_n(q,\rho)$ be the fraction of $G_1,\dots,G_n$ inducing resolution $\rho$ on $q$, and let $\widehat T_n$ be any maximizer of the [total quartet support](quartet-score.md) $\sum_q f_n(q,T|_q)$ over all unrooted binary trees $T$ on $X$. Then almost surely, for all sufficiently large $n$, every such maximizer is isomorphic to $S$ as an unrooted tree on $X$.

The statement concerns the unrooted topology only: quartets do not identify the root. It does not cover estimated gene trees, nor optimization restricted to a constrained search space. When some internal length is $0$, the three resolutions of an affected quartet each have probability $\frac13$ and the binary resolution is not identifiable; that case is excluded. Independence of the loci is needed: if one random gene tree is repeated at every locus, the empirical frequencies are those of a single draw and need not converge to the coalescent probabilities. For four taxa the statement reduces to the four-taxon analogue of [three-species concordance](../../coalescent-theory/multispecies-coalescent/gene-tree-prob-triple-matching.md).

## Depends on

- [Total quartet support of a tree](quartet-score.md)
- [Empirical quartet frequencies eventually recover the species quartets](positive-quartet-margin-and-eventual-strict-plur.md)
- [Under strict plurality other topologies have smaller support](quartet-score-lt-of-not-iso.md)

## Expansion

A proof page combines the two dependencies: the first gives, almost surely, an $n_0$ such that $f_n$ is a strict plurality for $S$ for all $n\ge n_0$; the second then gives $\sum_qf_n(q,T|_q)<\sum_qf_n(q,S|_q)$ for every $T$ not isomorphic to $S$, so every maximizer is isomorphic to $S$. It should also record the excluded boundary case $t_q=0$ and the repeated-gene-tree counter-probe.

## Sources

- S. Mirarab, R. Reaz, Md. S. Bayzid, T. Zimmermann, M. S. Swenson and T. Warnow, *ASTRAL: genome-scale coalescent-based species tree estimation*, Bioinformatics 30 (2014), i541–i548 (quartet-support maximization).
- E. S. Allman, J. H. Degnan and J. A. Rhodes, *Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent*, Journal of Mathematical Biology 62 (2011), 833–862 (quartet identifiability and unrooted quartet probabilities).
