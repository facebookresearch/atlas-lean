# Clade probabilities determine expected STAR distances

Let $\sigma = (\psi,\lambda)$ be an $n$-taxon rooted binary metric species tree, let rooted gene-tree topologies arise under the multispecies coalescent, and for a set $\mathcal{C}$ of taxa let $\mathbb{P}_\sigma(\mathcal{C})$ be the probability that $\mathcal{C}$ is a clade (the leaf set of the subtree below some node) of the random gene tree. Let $D_T$ be the STAR distance matrix of a gene tree $T$ under a node numbering sequence that depends only on node depth (as in the generalized STAR method). Then:

1. The clade probabilities $\{\mathbb{P}_\sigma(\mathcal{C})\}$ determine the expected STAR distance matrix $\mathbb{E}_\sigma(D_T)$ (Proposition 5.1).
2. The rooted species tree topology $\psi$ is identifiable from the clade probabilities under the multispecies coalescent (Corollary 5.2).

## Depends on

- [Consistency of generalized STAR node numberings](consistency-of-generalized-star-node-numberings.md)

## Expansion

With edge-length sequence $b_i = a_{i-1} - a_i$, the STAR distance between taxa $x$ and $y$ is a sum over the internal edges of the gene tree that lie on the path between them, each weighted by a function of its depth. The depth of the edge above a clade and whether it separates $x$ from $y$ are determined by the clades of the gene tree, so taking expectations expresses $\mathbb{E}_\sigma(D_T)(x,y)$ as a linear combination of clade probabilities. Identifiability then follows from the previous result: the expected matrix strongly fits $\psi$ ultrametrically, so it determines $\psi$. This reinterprets STAR as a consensus method based on clades: it uses only how often each set of taxa forms a gene-tree clade, combined with depth weights.

## Sources

- Elizabeth S. Allman, James H. Degnan, John A. Rhodes, Species tree inference by the STAR method, and generalizations, arXiv:1204.4413 (2012). <https://doi.org/10.48550/arXiv.1204.4413>. Published version: Journal of Computational Biology 20(1) (2013), 50–61, <https://doi.org/10.1089/cmb.2012.0101>; locators above refer to the arXiv version.
