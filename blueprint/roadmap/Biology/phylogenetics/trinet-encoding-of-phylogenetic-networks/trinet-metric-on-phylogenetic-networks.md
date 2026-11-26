# Trinet metric on phylogenetic networks

Let $X$ be a finite set with $|X| \ge 3$ and let $\mathcal{N}$ be the class of binary recoverable rooted phylogenetic networks on $X$ each of whose biconnected components has at most two reticulations, or is tree-child, or has at most three outgoing cut-arcs (networks are identified up to leaf-label-preserving isomorphism). For $N \in \mathcal{N}$ let $\mathrm{Tn}(N)$ be its set of exhibited trinets.

**Corollary.** The map $d : \mathcal{N} \times \mathcal{N} \to \mathbb{R}$,

$$d(N, N') = \bigl|\mathrm{Tn}(N) \,\triangle\, \mathrm{Tn}(N')\bigr|,$$

where $\triangle$ is the symmetric difference, is a metric on $\mathcal{N}$. In particular it is a metric on binary recoverable level-2 networks and on binary tree-child networks on $X$.

## Depends on

- [Trinets encode level-2 and tree-child networks](trinets-encode-level-2-and-tree-child-networks.md)

## Expansion

The cardinality of a symmetric difference of finite sets is always a pseudometric: it is symmetric, vanishes on equal sets, and satisfies the triangle inequality because $A \triangle C \subseteq (A \triangle B) \cup (B \triangle C)$. The only property that can fail is definiteness, $d(N, N') = 0 \Rightarrow N = N'$. On $\mathcal{N}$ this is exactly the statement that every network in the class is encoded by its trinets. The metric is computable in time polynomial in $|X|$ once the trinets are known, since there are $\binom{|X|}{3}$ of them.

## Sources

- L. van Iersel and V. Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), <https://doi.org/10.1007/s00285-013-0683-5>. Corollary 3 (Section 6).
