# Identifiability of blob circular orders from average genetic distances

**Setting.** Let $N^+$ be a rooted metric binary phylogenetic network that is outer-labeled planar (each blob has an embedding with its articulation nodes on the outer face). Gene trees arise under one of three models: DT (each gene tree is a tree displayed by the network, with branch lengths from the network), NMSCcom (network multispecies coalescent with common inheritance across a reticulation's parental lineages) or NMSCind (network multispecies coalescent with independent inheritance). Under NMSCind assume NoAnomAD: no induced 4-taxon network is average-distance-anomalous. The data are the average pairwise genetic distances $\bar d(a,b)$ over gene trees. For four taxa, let $SP_{abcd}$ be the vector of the three pairwise sums $\bar d(a,b) + \bar d(c,d)$, $\bar d(a,c) + \bar d(b,d)$, $\bar d(a,d) + \bar d(b,c)$.

**Theorem.** Under each of DT, NMSCcom and NMSCind + NoAnomAD:

1. For quartets taken from a $B$-informative set of a blob $B$, if only $ab|cd$ is displayed then $SP_{abcd} = (p,q,q)$ with $p < q$ and the quartet network has a cut edge splitting $ab|cd$; if both $ab|cd$ and $ac|bd$ are displayed then $SP_{abcd} = (p,q,r)$ with $p, q < r$ and the quartet network has a 4-blob with circular order $(a,b,d,c)$.
2. Hence the reduced unrooted tree of blobs of $N^+$ and the circular order of the articulation nodes of every blob are identifiable from the average pairwise distances.

## Expansion

Average distances are mixtures, over displayed trees or gene trees, of tree metrics. For a 4-blob that displays two quartet topologies, the two smallest of the three pairwise sums correspond to the displayed splits and the largest to the split incompatible with the circular order, so the four-point condition read on averages reveals the order. A cut-edge quartet gives a tree-like pattern with a tie. Collecting these quartet orders over a $B$-informative set and applying the quartet-to-circular-order theorem recovers each blob's order, while the tree-like quartets recover the tree of blobs.

## Depends on

- [Uniqueness of the circular order of an outer-labeled planar blob](uniqueness-of-the-circular-order-of-an-outer-labeled-planar-blob.md)
- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](../../../../coalescent-theory/multispecies-coalescent/tree-of-blobs-identifiability/blob-and-tree-of-blobs-of-a-phylogenetic-network.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../../../../coalescent-theory/multispecies-coalescent/network-multispecies-coalescent-fixed-network-ge.md)

## Sources

- John A. Rhodes, Hector Banos, Jingcheng Xu and Cécile Ané, "Identifying circular orders for blobs in phylogenetic networks", Advances in Applied Mathematics 163 (2025), 102804, <https://doi.org/10.1016/j.aam.2024.102804>; numbering as in arXiv:2402.11693: Propositions 6.1, 6.2 and Corollary 6.3.
