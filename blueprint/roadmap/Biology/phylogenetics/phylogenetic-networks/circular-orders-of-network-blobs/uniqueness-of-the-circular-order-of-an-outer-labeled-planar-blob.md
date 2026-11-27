# Uniqueness of the circular order of an outer-labeled planar blob

**Setting.** A *blob* of a phylogenetic network is a maximal biconnected subgraph (one with no cut node) containing at least one cycle; its *articulation nodes* are the nodes where the rest of the network (pendant subnetworks carrying taxa) attaches. A graph $G$ is *outer-labeled planar* for a vertex subset $V_0$ if it has a planar embedding with every vertex of $V_0$ on the outer face (the frontier). The frontier of such an embedding visits the vertices of $V_0$ in a cyclic sequence, the induced *circular order* of $V_0$.

**Theorem.** Let $G$ be an undirected biconnected graph that is outer-labeled planar for $V_0 \subseteq V(G)$. Then the frontiers of all planar embeddings of $G$ with $V_0$ on the frontier induce the same circular order of $V_0$ (up to reversal). Consequently, every outer-labeled planar blob of a phylogenetic network has a unique circular order of its articulation nodes, the one induced by any outer-labeled planar embedding of the blob.

**Recovery from quartets.** For a binary outer-labeled planar blob $B$, the circular orders of the induced 4-taxon (quartet) networks on a full $B$-informative collection of 4-taxon sets (one taxon below each of four distinct articulation nodes, covering all quadruples of articulation nodes) determine the circular order of the articulation nodes of $B$. Only quartets inducing a 4-blob are needed.

## Expansion

Adding a new vertex adjacent to every vertex of $V_0$ turns outer-labeled planarity into ordinary planarity of a biconnected graph, and in a planar embedding of a biconnected graph the neighbors of a vertex appear in an order constrained by Whitney-type uniqueness arguments on 3-connected components; the possible flips of 2-separations cannot reorder vertices that all lie on the outer face. The quartet result then follows because a circular order on $m \ge 4$ points is determined by its restrictions to all 4-subsets, and each 4-blob in an induced quartet network carries exactly the restriction of the blob's order.

## Sources

- John A. Rhodes, Hector Banos, Jingcheng Xu and Cécile Ané, "Identifying circular orders for blobs in phylogenetic networks", Advances in Applied Mathematics 163 (2025), 102804, <https://doi.org/10.1016/j.aam.2024.102804>; numbering as in arXiv:2402.11693: Theorem 4.1, Corollary 4.2 and Theorem 5.3.
