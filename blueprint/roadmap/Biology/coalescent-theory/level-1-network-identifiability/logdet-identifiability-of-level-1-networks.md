# Identifiability of level-1 network topology from logDet distances

Let $N^+$ be a binary level-1 ultrametric rooted network on a taxon set $X$ with $|X| \ge 3$, and let $\widetilde N$ be its topological LSA network (the network below the lowest stable ancestor of $X$, with that node as root) modulo 2- and 3-cycles and the directions of edges in 4-cycles.

**Theorem.** Under the mixture of coalescent mixtures model on $N^+$, for generic hybridization parameters, $\widetilde N$ is identifiable from the theoretical logDet distances $d_{LD}(x, y)$ for pairs of taxa $x, y \in X$.

The same conclusion holds (i) for multisite genes evolving on a common tree with independently drawn gene lengths, and (ii) for the non-coalescent limit in which every gene tree is displayed on the network (population sizes tending to $0$).

## Expansion

By the [rooted-triple propositions](logdet-distances-on-rooted-triple-networks.md), for generic parameters the three logDet distances on any three taxa are pairwise distinct if and only if the induced rooted triple network has a 4-cycle, and then the largest distance determines the unrooted topology of the 4-cycle; otherwise the two equal distances identify the rooted triple $((a,b),c)$. This determines the set of undirected rooted triple networks displayed on $N^+$ with 2- and 3-cycles suppressed, and that set determines the LSA network modulo 2- and 3-cycles and 4-cycle directions (the authors' Proposition 1, proved by assembling rooted quartet networks from the triples).

## Depends on

- [LogDet distances on rooted triple networks](logdet-distances-on-rooted-triple-networks.md)

## Sources

- E. S. Allman, H. Baños and J. A. Rhodes, "Identifiability of species network topologies from genomic sequences using the logDet distance", *Journal of Mathematical Biology* 84 (2022), <https://doi.org/10.1007/s00285-022-01734-2> (PMC9192096). Definition 7, Proposition 1, Theorem 1 and its proof, Section 6 (variations).
