# Quarnet detection of cut-edge splits and blob-tree encoding

**Setting.** A *semi-directed (binary) phylogenetic network* $N$ on a finite leaf set $X$ is the mixed graph obtained from a rooted binary phylogenetic network by undirecting every arc except those entering reticulations and suppressing the root; it has no parallel arcs, no degree-2 vertices, and no blob (maximal 2-edge-connected subgraph with at least three vertices) with at most two incident edges/arcs. For $A\subseteq X$, $|A|\ge2$, the **restriction** $N|_A$ keeps the vertices lying on a **∧-path** between two leaves of $A$ (a sequence of distinct vertices $(v_1,\dots,v_p)$ such that, for some $i$, both $(v_i,\dots,v_1)$ and $(v_i,\dots,v_p)$ are semi-directed paths) and then applies the suppression operations; $N|_A$ is again a semi-directed phylogenetic network. A **quarnet** is a semi-directed phylogenetic network with four leaves, and $Q(N)=\{N|_A: A\subseteq X,\ |A|=4\}$. A split $A|B$ of $X$ is a **cut-edge split** (CE-split) of $N$ if deleting some cut-edge of $N$ leaves two components with leaf sets $A$ and $B$. The **blob tree** $B(N)$ is the unrooted tree obtained by contracting every blob of $N$ to a single vertex.

**Theorem (quarnet test for splits).** Let $N$ be a semi-directed binary phylogenetic network on $X$ (of any level) and $A|B$ a split of $X$. Then $A|B$ is a CE-split of $N$ if and only if either $A|B$ is trivial ($|A|=1$ or $|B|=1$), or $A|B$ is non-trivial and for all pairwise distinct $a_1,a_2\in A$, $b_1,b_2\in B$,

$$\{a_1,a_2\}\,|\,\{b_1,b_2\}\ \text{ is a CE-split of } N|_{\{a_1,a_2,b_1,b_2\}} .$$

**Corollary (blob-tree encoding).** If $N$ and $N'$ are semi-directed phylogenetic networks on $X$ with the same set of quarnets (up to isomorphism), then $B(N)\cong B(N')$.

## Depends on

- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](../../../../coalescent-theory/multispecies-coalescent/tree-of-blobs-identifiability/blob-and-tree-of-blobs-of-a-phylogenetic-network.md)

## Expansion

The CE-splits of $N$ are exactly the splits of its blob tree, and an unrooted phylogenetic tree is determined by its splits, so the corollary follows from the theorem. The "only if" direction holds because restriction preserves a cut-edge separating $a_1,a_2$ from $b_1,b_2$. The main work is the converse when $N$ is simple: then every non-trivial split fails to be a CE-split, and one must exhibit $a_1,a_2\in A$, $b_1,b_2\in B$ whose quarnet keeps a blob separating neither pair. This is done on a rooting of $N$, using that in a simple network every non-root, non-leaf vertex has an arc entering its descendant set from outside, and that every arc lies on one of two arc-disjoint directed paths ending at a leaf-reticulation; these paths survive restriction to suitably chosen leaves. The general case reduces to the simple one by restricting to a blob. The result places no restriction on the level, which is why the coarse tree-like structure of a network is identifiable from four-taxon information even when the full network is not; it underlies consistency proofs for quarnet-based network reconstruction.

## Sources

- Katharina T. Huber, Leo van Iersel, Mark Jones, Vincent Moulton and Leonie Veenema - Nipius, "When are Quarnets Sufficient to Reconstruct Semi-directed Phylogenetic Networks?", Bulletin of Mathematical Biology 87 (2025), 136, <https://doi.org/10.1007/s11538-025-01510-5>; numbering as in arXiv:2408.12997: Section 3 (Proposition 3.4, restrictions) and Section 5 (Theorem 5.1, Corollary 5.6).
