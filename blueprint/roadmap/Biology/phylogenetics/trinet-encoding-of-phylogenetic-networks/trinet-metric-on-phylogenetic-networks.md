# Trinet metric on phylogenetic networks

Let $X$ be a finite set with $|X| \ge 3$ and let $\mathcal{N}$ be the class of binary recoverable rooted phylogenetic networks on $X$, in the sense of [trinets and cut-arc sets](trinets-and-cut-arc-sets.md) (no in-degree-$1$ out-degree-$1$ vertices, a root of out-degree at least $2$), each of whose biconnected components has at most two reticulations, or is tree-child, or has at most three outgoing cut-arcs; networks are identified up to leaf-label-preserving isomorphism. For $N \in \mathcal{N}$ let $\mathrm{Tn}(N)$ be its set of exhibited trinets.

**Corollary.** The map $d : \mathcal{N} \times \mathcal{N} \to \mathbb{R}$,

$$d(N, N') = \bigl|\mathrm{Tn}(N) \,\triangle\, \mathrm{Tn}(N')\bigr|,$$

where $\triangle$ is the symmetric difference, is a metric on $\mathcal{N}$. In particular it is a metric on binary recoverable level-2 networks and on binary tree-child networks on $X$.

## Depends on

- [Trinets and cut-arc sets of a phylogenetic network](trinets-and-cut-arc-sets.md)

## Proof depends on

- [Trinets encode level-2 and tree-child networks](trinets-encode-level-2-and-tree-child-networks.md)

## Expansion

The cardinality of a symmetric difference of finite sets is always a pseudometric: it is symmetric, vanishes on equal sets, and satisfies the triangle inequality because $A \triangle C \subseteq (A \triangle B) \cup (B \triangle C)$. The only property that can fail is definiteness, $d(N, N') = 0 \Rightarrow N = N'$. It follows from the encoding theorem, which is stronger than needed: each $N \in \mathcal{N}$ is distinguished by its trinets from every recoverable network, not only from the members of $\mathcal{N}$. Definiteness on $\mathcal{N}$ alone would not imply that encoding statement. Each network exhibits exactly one trinet on each $3$-subset of $X$, so computing $d$ takes $2\binom{|X|}{3}$ trinet extractions and $\binom{|X|}{3}$ comparisons of the two trinets on a common leaf triple. This counts comparisons, not their cost: recoverable level-2 trinets on three leaves can be arbitrarily large, so the cost of each comparison (an isomorphism test, or the construction of a canonical form) must be bounded separately.

## Sources

- L. van Iersel and V. Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), <https://doi.org/10.1007/s00285-013-0683-5> (arXiv:1210.0362). Section 2 (number of level-2 trinets), Corollaries 2 and 3 (Section 6).
