# Two-cycles of a level-1 network are not identifiable from quartet CFs

A binary phylogenetic network, rooted or semidirected, is **level-1** if no two cycles of its underlying
undirected graph share a node. In a level-1 network a cycle made of $m$ edges, two of them hybrid, is an
**$m$-cycle**, and an **$m_k$-cycle** if exactly $k$ taxa descend from its hybrid node. Parameterize a
metric network by its **edge probabilities** $\ell = e^{-t} \in (0,1]$, where $t$ is the edge length in
coalescent units, so that $\ell$ is the probability that two lineages entering the edge do not coalesce
within it, together with the inheritance probabilities $\gamma$ at the hybrid nodes. All quartet
concordance factors are then polynomials in the $\ell$ and $\gamma$ parameters.

Let $\mathcal{N}^+$ be a level-1 rooted binary metric network containing a $2$-cycle, that is a pair of
parallel hybrid edges, with edge probabilities $h_1, h_2$ and inheritance parameters
$\gamma_1, \gamma_2 = 1 - \gamma_1$. Under the network multispecies coalescent, every quartet concordance
factor of $\mathcal{N}^+$ is unchanged when that $2$-cycle is replaced by a single edge with edge
probability $\ell \in (0,1]$ determined by

$$1 - \ell = \gamma_1^2(1 - h_1) + (1-\gamma_1)^2(1 - h_2).$$

Zero hybrid-edge lengths are allowed: $h_1 = h_2 = 1$ gives $\ell = 1$, a replacement edge of length $0$. Since $\ell$ sweeps all of $(0,1]$ as the $2$-cycle parameters vary, a topological level-1
network carrying a $2$-cycle cannot be distinguished from the network obtained by replacing that cycle
with an edge.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [Quartet concordance factors depend only on the unrooted quartet network](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)

## Proof depends on

- [A degree-2 sub-blob can be replaced by a single edge without changing quartet CFs](two-sub-blob-replacement-preserves-quartet-cfs.md)

## Expansion

Two lineages entering the $2$-cycle fail to coalesce inside it exactly when they either take different
parent edges, which under independent inheritance happens with probability $2\gamma_1(1-\gamma_1)$, or
take the same parent edge and fail to coalesce along it, with probability
$\gamma_1^2 h_1 + (1-\gamma_1)^2 h_2$. Adding these gives the displayed identity for $\ell$. Nothing else
about the cycle enters any quartet concordance factor, so the replacement is invisible in the data, and
the identity realizes every value of $\ell$ in $(0,1]$, including $\ell = 1$ when both hybrid edges have length $0$.

## Sources

- E. S. Allman, H. Baños, M. Garrote-López and J. A. Rhodes, "Identifiability of level-1 species networks from gene tree quartets", Bulletin of Mathematical Biology 86 (2024), 110, <https://doi.org/10.1007/s11538-024-01339-4> (PMC11272829). (Definition 2, Lemma 4, Corollary 5.)
