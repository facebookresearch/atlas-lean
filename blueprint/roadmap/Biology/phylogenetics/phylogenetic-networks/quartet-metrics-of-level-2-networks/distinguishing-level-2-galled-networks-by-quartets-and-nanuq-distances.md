# Distinguishing level-2 galled networks by quartets and NANUQ distances

**Setting.** Let $\mathcal N_2$ be the class of semi-directed phylogenetic networks on a leaf set $X$ that are level-2 (each blob has at most two reticulations), outer-labeled planar (an embedding in the plane with leaves on the outer face) and galled (every reticulation lies in a tree cycle), and $\mathcal B_2\subseteq\mathcal N_2$ its bloblet networks (a single nontrivial blob with all leaves attached to it). For $N$ let $\mathcal T(N)$ be its displayed trees, $\mathcal Q(N)$ the quartet trees they induce, and $d_N$ the NANUQ metric of [Circular decomposability of quartet-based network metrics](circular-decomposability-of-quartet-based-network-metrics.md). A $k$-blob is a blob with $k$ incident cut edges. In an outer-labeled planar network a $k$-blob ($k\ge4$) induces a circular order of the subnetworks around it; its *representative cycle* is the undirected $k$-cycle inducing that order.

**Canonical form.** The canonical form $N^c$ of $N\in\mathcal N_2$ is the mixed graph obtained by applying, in order:
1. contract every 2-blob;
2. contract every 3-blob;
3. replace every 4-blob by its representative cycle;
4. replace every *split symmetric* 5-blob (the 5-blob whose displayed-tree splits are invariant under cyclically permuting its leaves, Figure 8(b) of the source) by its representative cycle;
5. contract 3-cycles in $k$-blobs, $k\ge5$;
6. in $k$-blobs, $k\ge5$, with hybrid nodes $u,v$, suppress every *dts-undetectable 4-cycle* $(p_u,u,p'_u,w)$, a 4-cycle containing $u$ and a parent of $v$, with $p_u,p'_u$ the parents of $u$, $p_u$ and $u$ articulation nodes of the blob, and one of $p'_u,w$ a parent of $v$: delete the hybrid edge $(p_u,u)$, undirect $(p'_u,u)$, and suppress the two resulting degree-2 nodes;
7. in $k$-blobs, $k\ge6$, that are not split symmetric and have no dts-undetectable 4-cycle, contract the *dts-undetectable edge*, if any: a frontier edge $\{s,t\}$ (a non-hybrid edge of the blob incident to an articulation node) such that $s$ and $t$ are both parents of a hybrid of the blob, or $s$ is a parent of a hybrid and $t$ lies on a 4-cycle of the blob;
8. undirect the remaining 4-cycles in $k$-blobs, $k\ge6$.

Each operation acts on one blob, so $N^c$ is unique.

**Theorem.** (a) For $N_1,N_2\in\mathcal N_2$ on the same leaf set, the following are equivalent: $N_1^c\cong N_2^c$; $\mathcal Q(N_1)=\mathcal Q(N_2)$; $\mathrm{Split}(\mathcal T(N_1))=\mathrm{Split}(\mathcal T(N_2))$. So $N_1,N_2$ are distinguishable from their displayed quartets iff their canonical forms differ.

(b) If moreover $N_1,N_2\in\mathcal B_2$ and $|X|\ge4$, these are also equivalent to $d_{N_1}=d_{N_2}$: two such bloblets are distinguishable from their pairwise NANUQ distances iff their canonical forms differ.

## Depends on

- [Circular decomposability of quartet-based network metrics](circular-decomposability-of-quartet-based-network-metrics.md)
- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](../../../coalescent-theory/multispecies-coalescent/tree-of-blobs-identifiability/blob-and-tree-of-blobs-of-a-phylogenetic-network.md)

## Expansion

Displayed quartets and the split system of the displayed trees determine each other through the displayed quartet metric, whose support is $\mathrm{Split}(\mathcal T(N))$; this gives the equivalence of the three conditions in (a). The remaining work is to show that, up to the contractions defining the canonical form, an outer-labeled planar galled level-2 network is determined by that split system. In (b) the NANUQ metric has the same support on bloblets, and its split weights additionally separate configurations with equal displayed splits; for example, the pairwise NANUQ distances already distinguish the five canonical classes of 6-taxon level-2 bloblets.

## Sources

- N. Holtgrefe, E. S. Allman, H. Baños, L. van Iersel, "Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances", *Bulletin of Mathematical Biology* 87(12) (2025), 168, Section 5 (Definition 5.1, Proposition 5.3, Theorem 5.4), Section 6, <https://doi.org/10.1007/s11538-025-01549-4> (preprint arXiv:2507.17308).
