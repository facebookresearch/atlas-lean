# Identifiability of the tree of blobs under the network multispecies coalescent

Let $\mathcal{N}^+$ be an $n$-taxon rooted binary phylogenetic network ($n \ge 4$) under the
network multispecies coalescent (NMSC). Then for generic numerical parameters:
1. Every [B-quartet](blob-and-tree-of-blobs-of-a-phylogenetic-network.md) on $\mathcal{N}^+$ is identifiable from the quartet concordance factors $\{\mathrm{CF}_Q : Q \subseteq X,\, |Q| = 4\}$ by applying [4-blob CF-detectability](cf-detectability-of-4-blobs.md) to all induced 4-taxon networks followed by repeated application of the [B-quartet inference rule](b-quartet-inference-rule.md).
2. Consequently, the reduced unrooted tree of blobs $T_{\mathrm{rd}}(\mathcal{N}^-)$ is uniquely identifiable from the distribution of gene quartet topologies under the NMSC model.

## Depends on

- [Concordance-factor detectability of 4-blobs on 4-taxon networks](cf-detectability-of-4-blobs.md)
- [B-quartet inference rule on phylogenetic networks](b-quartet-inference-rule.md)

## Expansion

Part 1 proceeds by induction on $n$, with base case $n = 4$ given by Theorem 1. For $n \ge 5$, if a
B-quartet $\{a, b, c, d\}$ is not directly CF-detectable on its induced 4-taxon network, then some
other taxon $\alpha \in X \setminus \{a, b, c, d\}$ witnesses a cut edge in the network without
$\alpha$; applying the inductive hypothesis to $X \setminus \{d\}$ and $X \setminus \{a\}$
identifies $\{a, b, c, \alpha\}$ and $\{b, c, d, \alpha\}$ as B-quartets, and Theorem 2 then
forces $\{a, b, c, d\}$ to be a B-quartet. Part 2 follows because the collection of all resolved
and unresolved displayed quartets uniquely determines an unrooted (possibly multifurcating) phylogenetic tree.

## Sources

- E. S. Allman, H. Baños, J. D. Mitchell, and J. A. Rhodes, "The tree of blobs of a species network: identifiability under the coalescent", Journal of Mathematical Biology 86 (2023), 10 (published online 2022), <https://doi.org/10.1007/s00285-022-01838-9> (PMC10062380). (Theorems 3 and 4.)
