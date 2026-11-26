# Level-$k$ tree-child networks are reconstructible from their maximum lower-level subnetworks

**Networks.** A (rooted binary) phylogenetic network $N$ on a leaf set $X$ is a rooted acyclic digraph whose leaves are bijectively labelled by $X$; a *reticulation* has in-degree $2$, and the edges into a reticulation are *reticulation edges*. $N$ is *tree-child* if every non-leaf node has a child that is a tree node or a leaf. A *blob* is a biconnected component (maximal subgraph with at least three nodes and no cut-node of its own) or a tree node not in one; $N$ is *level-$k$* if the largest number of reticulations in a biconnected component is $k$.

**Edge deletion.** *Cleaning up* a directed acyclic graph repeatedly deletes unlabelled out-degree-$0$ nodes, suppresses in-degree-$1$ out-degree-$1$ nodes, and replaces parallel edge pairs by a single edge (suppressing both endpoints). Deleting a reticulation edge and cleaning up gives a subnetwork. The deletion is *valid* if the cleaned-up subnetwork has exactly $2$ nodes and $3$ edges fewer than $N$, i.e. only the edge is removed and its endpoints are suppressed. For $k \ge 1$, a *maximum lower-level subnetwork (MLLS)* of a level-$k$ network $N$ is obtained by deleting exactly one valid reticulation edge from every level-$k$ blob of $N$; write $\mathcal{N}^{mlls}(N)$ for the set of all of them. A class $\mathcal{C}$ is *MLLS-reconstructible* if $N, N' \in \mathcal{C}$ and $\mathcal{N}^{mlls}(N) = \mathcal{N}^{mlls}(N')$ imply that $N$ and $N'$ are isomorphic (as leaf-labelled digraphs).

**Theorem.** Let $k \ge 2$.

1. The class of binary level-$k$ tree-child networks is MLLS-reconstructible.
2. Given $\mathcal{T} = \mathcal{N}^{mlls}(N)$ for a level-$k$ tree-child network $N$ on $X$, a bottom-up algorithm reconstructs $N$ in time $O(|\mathcal{T}|\,|X|^3/k)$.
3. If the number of level-$k$ blobs of $N$ is known, three MLLSs suffice to reconstruct $N$.

Since every MLLS is a subnetwork of level at most $k-1$, MLLS-reconstructibility implies level-reconstructibility (reconstructibility from all lower-level subnetworks). Every subnetwork obtained from a tree-child network by one reticulation edge deletion is again tree-child.

## Expansion

The proof first recovers the *blob tree* $BT(N)$ (the tree obtained by contracting each blob to a node labelled by the leaves below it): for a level-$k$ valid network a set $A \subseteq X$ labels a blob node of $BT(N)$ iff it does so in $BT(N^{mlls})$ for every MLLS. It then examines each pair of leaves $\{x,y\}$: the five local shapes in which two leaves can sit inside a tree-child blob (named $\Lambda$, $\lambda$, $A$, $H$, $\Pi$ in the source) each survive into some MLLS, and the shape on $\{x,y\}$ in $N$ is identifiable from the shapes in the MLLSs. The level-$k$ blobs are then rebuilt by reinserting reticulation edges between identified pairs, working upward from reticulated cherries. The theorem is stated for $k \ge 2$; for level-$1$ networks the source points to earlier results, which need extra hypotheses such as girth at least $5$ for reconstruction from triplets.

## Sources

- Y. Murakami, L. van Iersel, R. Janssen, M. Jones, V. Moulton, "Reconstructing Tree-Child Networks from Reticulate-Edge-Deleted Subnetworks", arXiv:1811.06777 (2018): Section 2 (definitions of valid deletions, MLLS, MLLS-reconstructibility), Theorems 1–3 (blob-tree reconstruction), Theorems 4–5 (leaf-pair shapes), Theorem 6 (MLLS-reconstructibility), Theorems 7–8 (algorithm and three MLLSs). <https://doi.org/10.48550/arXiv.1811.06777> Published version: Bulletin of Mathematical Biology 81 (2019) 3823–3863, <https://doi.org/10.1007/s11538-019-00641-w>.
