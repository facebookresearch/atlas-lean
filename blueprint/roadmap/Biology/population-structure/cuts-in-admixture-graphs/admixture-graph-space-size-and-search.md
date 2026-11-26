# Admixture-graph space size and search

This node covers the size of the search space for admixture graphs on a fixed set of populations.

Let $X$ be a finite set of $n\ge1$ populations. By [Schröder's count](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-rooted-binary-tree.md), the number of [rooted binary phylogenetic trees](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/rooted-binary-tree.md) on $X$ is $(2n-3)!!=1\cdot3\cdots(2n-3)$, with value $1$ for $n=1$; for $n=5$ it is $105$. For $n\ge2$, an admixture graph with $k$ admixture events on $X$ is taken here to be a finite rooted acyclic directed graph whose root has out-degree $2$, whose leaves (in-degree $1$, out-degree $0$) are labeled bijectively by $X$, and whose other vertices are tree vertices (in-degree $1$, out-degree $2$) or exactly $k$ admixture vertices (in-degree $2$, out-degree $1$); counting edges by in- and out-degrees shows that it has exactly $n+k-2$ tree vertices. Hence for fixed $X$ and $k$ there are finitely many such graphs up to label-preserving isomorphism, and for any real-valued score (for example a fit statistic computed from $f$-statistics) a best-scoring graph exists: "best-scoring graph" denotes a maximizer over this finite set. The computational complexity of finding it is a separate question.

The target also asks for a lower bound showing that, for each $k$, admixture graphs with $k$ admixture events on $X$ are at least as numerous as rooted binary trees on $X$. Its exact form depends on the conventions (whether parallel edges are allowed, and the range of $n$ and $k$), and is not stated by the cited source.

## Depends on

- [Schröder's count of rooted binary phylogenetic trees](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-rooted-binary-tree.md)

## Expansion

An expansion states separately, with hypotheses fixed from a source:

- the definition of an admixture graph with $k$ admixture events and its isomorphism notion, matching the models fitted to $f$-statistics;
- the vertex count and the resulting finiteness of the set of graphs for fixed $X$ and $k$, so that a best-scoring graph exists;
- the lower bound by an injection from rooted binary trees into graphs with $k$ admixture events, with its range of validity in $n$ and $k$;
- a computational check of $(2n-3)!!$ for $n\le5$.

Prerequisites:

- [Schröder's count of rooted binary phylogenetic trees](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-rooted-binary-tree.md)
- Finite partitions and combinatorics

## Sources

- R. Maier, P. Flegontov, O. Flegontova, U. Isildak, P. Changmai and D. Reich, *On the limits of fitting complex models of population history to f-statistics*, eLife 12 (2023), e85492, <https://reich.hms.harvard.edu/sites/reich.hms.harvard.edu/files/inline-files/elife-85492-v2.pdf> (systematic search over the vast space of admixture graphs; the 105 branching orders of five populations; definitions).
