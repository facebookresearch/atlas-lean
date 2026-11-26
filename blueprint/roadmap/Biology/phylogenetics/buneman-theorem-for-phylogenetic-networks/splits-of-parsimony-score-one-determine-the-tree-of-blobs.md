# Splits of parsimony score one determine a network's tree of blobs

**Setting.** A phylogenetic $X$-network $N$ is a connected graph whose degree-one vertices are bijectively labeled by $X$. A binary character $f : X \to \{0,1\}$ induces the $X$-split $\sigma_f = f^{-1}(0)\,|\,f^{-1}(1)$. Its (hardwired) parsimony score is
$$l(f,N) = \min_g |\operatorname{ch}(g)|,$$
the minimum over extensions $g : V(N) \to \{0,1\}$ of $f$ of the number of edges whose endpoints get different states. Let $A_1(N) = \{f : l(f,N) = 1\}$ and $\Sigma(N) = \{\sigma_f : f \in A_1(N)\}$, the splits realizable with a single change. $N$ is *weakly proper* if no cut-edge induces the trivial partition $\varnothing\,|\,X$. The *tree of blobs* $T(N)$ is obtained by contracting every blob (maximal 2-edge-connected subgraph) to a vertex and suppressing degree-2 vertices.

**Buneman's theorem.** A set $\Sigma$ of $X$-splits containing all trivial splits equals $\Sigma(T)$ for some phylogenetic $X$-tree $T$ iff its splits are pairwise compatible, and two phylogenetic $X$-trees are isomorphic iff they have the same split set.

**Theorem (extension to networks).** Let $N, \widetilde N$ be weakly proper phylogenetic $X$-networks. Then $\Sigma(N) = \Sigma(T(N))$, and
$$\Sigma(N) = \Sigma(\widetilde N) \iff T(N) \cong T(\widetilde N).$$
Hence $A_1(N) = A_1(\widetilde N)$ iff the two networks have isomorphic trees of blobs, so single-change characters recover exactly the tree of blobs and nothing inside the blobs. If $N$ has no redundant edges, $T(N)$ is the contraction of all blob edges, its edges are exactly the cut-edges of $N$, and $\Sigma(T(N))$ is the set of splits induced by those cut-edges.

**Corollary (small galled trees).** If $N, \widetilde N$ are galled $X$-trees whose cycles are all simple of length at most $5$, then $l(f, N) = l(f, \widetilde N)$ for every binary character $f$ iff $T(N) \cong T(\widetilde N)$; so even the full parsimony profile cannot distinguish such networks beyond their tree of blobs.

## Depends on

- [Buneman split index and split weights of a tree metric](../neighbor-joining/buneman-split-index-and-split-weights-of-a-tree.md)

## Expansion

A character with one change along a cut-edge induces that edge's split, so cut-edge splits lie in $\Sigma(N)$. Conversely, a single change on an edge inside a blob leaves the two endpoints connected by another path, which must also carry a change; so one change can only occur on a cut-edge, and $\Sigma(N)$ is the set of cut-edge splits, which are precisely the splits of the tree of blobs. Buneman's theorem for trees then identifies $T(N)$ from its splits. Weak properness excludes cut-edges with all leaves on one side, which would produce a trivial "split" with an empty part; redundant edges are removed by contraction without changing the induced splits.

## Sources

- M. Wilde and M. Fischer, "An extension of the classic Buneman theorem from phylogenetic trees to networks", arXiv:2610.41725 (2026), Theorems 1, 2 and Corollaries 8, 11, 12, 15, <https://doi.org/10.48550/arXiv.2610.41725>.
