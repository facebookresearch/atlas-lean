# Clade probabilities determine expected STAR distances

Let $\sigma = (\psi,\lambda)$ be an $n$-taxon rooted binary metric species tree, let rooted gene-tree topologies arise under the multispecies coalescent, and for a set $\mathcal{C}$ of taxa let $\mathbb{P}_\sigma(\mathcal{C})$ be the probability that $\mathcal{C}$ is a clade (the leaf set of the subtree below some node) of the random gene tree. Let $D_T$ be the STAR distance matrix of a gene tree $T$ under the **standard** STAR node numbering, in which every internal edge of the remetrized gene tree has length $1$ and all leaves are at distance $n$ from the root, and let $c_T(a,b)$ be the number of non-trivial clades of $T$ containing both $a$ and $b$, so that $D_T(a,b) = 2\big(n - c_T(a,b)\big)$. Then:

1. The clade probabilities $\{\mathbb{P}_\sigma(\mathcal{C})\}$ determine the expected STAR distance matrix $\mathbb{E}_\sigma(D_T)$ (Proposition 5.1): for all taxa $a \ne b$,

$$\mathbb{E}_\sigma\big(D_T(a,b)\big) = 2n - 2\sum_{\substack{\mathcal C \text{ non-trivial}\\ a,b \in \mathcal C}} \mathbb{P}_\sigma(\mathcal C).$$

The statement is for the standard numbering only: for a general depth-based numbering the expected distance need not be a linear combination of clade probabilities (over the rooted binary $4$-taxon trees, the indicator that $\mathrm{MRCA}(a,b)$ lies at depth $2$ is not in the span of the clade indicators and the constant).
2. The rooted species tree topology $\psi$ is identifiable from the clade probabilities under the multispecies coalescent (Corollary 5.2).

## Depends on

- [Consistency of generalized STAR node numberings](consistency-of-generalized-star-node-numberings.md)

## Expansion

Under the standard numbering, the non-trivial clades containing $a$ and $b$ correspond to the non-root vertices on the path from the root to $\mathrm{MRCA}(a,b)$, so $c_T(a,b)$ is the distance from the root to $\mathrm{MRCA}(a,b)$ in the remetrized ultrametric tree and $D_T(a,b) = 2(n - c_T(a,b))$. Writing $c_T(a,b) = \sum_{\mathcal C} \mathbf 1\{T \text{ displays } \mathcal C\}\,\mathbf 1\{a,b \in \mathcal C\}$ and taking expectations gives the displayed identity. Identifiability then follows from the previous result: the expected matrix strongly fits $\psi$ ultrametrically, so it determines $\psi$. This reinterprets STAR as a consensus method based on clades: it uses only how often each set of taxa forms a gene-tree clade, combined with depth weights.

## Sources

- Elizabeth S. Allman, James H. Degnan, John A. Rhodes, Species tree inference by the STAR method, and generalizations, arXiv:1204.4413 (2012). <https://doi.org/10.48550/arXiv.1204.4413>. Published version: Journal of Computational Biology 20(1) (2013), 50–61, <https://doi.org/10.1089/cmb.2012.0101>; locators above refer to the arXiv version.
