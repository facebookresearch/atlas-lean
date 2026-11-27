# Identifiability of galled tree-child networks from quartet concordance factors

**Definitions.** A semidirected phylogenetic network is obtained from a rooted network by suppressing the root and undirecting tree edges while keeping hybrid edges directed. A **blob** is a maximal 2-edge-connected subgraph; contracting each blob gives the **tree of blobs**. A network is **galled** if each pair of partner hybrid edges lies on a cycle containing no other hybrid edge, and **tree-child** if every rooting compatible with it is tree-child. For a blob $B$ with generated bloblet $N(B)$ (the blob plus its incident cut edges) and leaf set $Y_0 \sqcup Y_\ell$, where $Y_\ell$ are the leaves below lowest nodes of $B$, say $B$ is in **class $C_k$** ($k \ge 3$) if $N(B)$ is reduced, galled, tree-child, all hybrid nodes have out-degree 1, and for every $y \in Y_\ell$ the internal blob of the reduced subnetwork on $Y_0 \cup \{y\}$ is a cycle of length at least $k$. A network is $C_k$ if it is reduced and all its blobs are $C_k$. These classes include networks of any level and non-planar networks.

The **quartet concordance factors** (CFs) of a network are, for every 4-taxon set, the probabilities of the three unrooted quartet gene-tree topologies.

**Theorem.** Let $N$ be a binary semidirected network in $C_4$. Under the network multispecies coalescent with independent or common inheritance across hybrid nodes, generic numerical parameters and 2 samples per taxon, the semidirected topology of $N$ and the lengths of internal tree edges in its blobs are identifiable from quartet CFs. With 1 sample per taxon, or under the displayed-tree model with CFs and metric gene trees, the same holds for binary networks in $C_5$.

**Hybrid-detection lemma.** In an extended bloblet with internal $C_5$ blob, taxon $x$ lies below a hybrid node if and only if there is a 4-taxon set $Y$ such that the tree of blobs of the network induced on $Y$ is resolved but that induced on $Y \cup \{x\}$ is a star.

## Expansion

The proof separates combinatorics from models. Combinatorially, a $C_4$ network is identifiable if one can identify (i) the tree of blobs, (ii) the circular order of taxa around a 4-cycle in a 4-taxon level-1 network, (iii) lengths of tree edges in such 4-cycles, and (iv) which taxa lie below hybrid nodes of a blob. In a galled tree-child bloblet the tree edges not leading to hybrid descendants form a fully labeled **root skeleton tree**, and each hybrid edge attaches to a point of it; edge lengths read off 4-taxon subnetworks locate these attachment points, reconstructing the blob. Each of (i)–(iv) is then verified for quartet CFs under the coalescent models; with two samples per taxon, nontrivial 3-blobs become detectable, which upgrades $C_5$ to $C_4$. Previously only level-1 networks were known to be identifiable from quartet CFs.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../../../coalescent-theory/multispecies-coalescent/network-multispecies-coalescent-fixed-network-ge.md)

## Sources

- E. S. Allman, C. Ané, H. Baños, J. A. Rhodes, "Beyond level-1: identifiability of a class of galled tree-child networks", Bulletin of Mathematical Biology (2025), Section 3 (Lemma 3.1, Definition 7), Section 4 (assumptions A-ToB, A-4circ, A-3blob, A-4len, A-hyb; Lemmas 4.1–4.2; Theorems 4.3, 4.5, 4.6) and Section 5 (Theorem 5.7, Proposition 5.8), <https://doi.org/10.1007/s11538-025-01545-8>, PMCID PMC12546270.
