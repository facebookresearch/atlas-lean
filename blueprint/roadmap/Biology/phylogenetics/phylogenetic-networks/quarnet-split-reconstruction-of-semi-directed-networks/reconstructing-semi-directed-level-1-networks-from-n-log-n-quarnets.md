# Reconstructing semi-directed level-1 networks from $O(n\log n)$ quarnets

**Setting.** A semi-directed phylogenetic network on leaf set $X$ is a partially directed graph obtained from a rooted network by suppressing the root and the orientation of tree edges; directed edges point into reticulation (hybridization) vertices. It is *level-1* if every blob (2-edge-connected component) contains at most one reticulation, i.e. cycles are vertex-disjoint. A *quarnet* is the semi-directed network induced on four leaves; a *quarnet-split* $a_1a_2 \mid b_1b_2$ records a split of the quarnet's tree-of-blobs. A bipartition $A \mid B$ of $X$ is a *split* of the network if it is induced by a cut-edge.

**Theorem.**

1. *(Splits from quarnet-splits.)* For a non-trivial partition $A \mid B$ and any $a_1 \in A$, $b_1 \in B$: $A \mid B$ is a split of the network iff $a_1a_2 \mid b_1b_2$ is a quarnet-split for all $a_2 \in A \setminus \{a_1\}$, $b_2 \in B \setminus \{b_1\}$.
2. *(Tree of blobs.)* From quarnet-splits, the tree-of-blobs of any semi-directed network on $n$ leaves can be reconstructed in $O(n^3)$ time using $O(n^3)$ quarnet-splits.
3. *(Level-1 networks.)* For a binary semi-directed level-1 network on $n \ge 4$ leaves:
   - (a) from its quarnets, the network can be reconstructed in $O(n^2)$ time using only $O(n\log n)$ quarnets;
   - (b) from quarnet-splits and four-cycle quarnets, it can be reconstructed up to placing reticulations in triangles and collapsing triangles, in $O(n^2)$ time with $O(n\log n)$ quarnet-splits and $O(n)$ four-cycle quarnets;
   - (c) from displayed quartets, it can be reconstructed up to placing reticulations in triangles and 4-cycles and collapsing triangles, in $O(n^2)$ time with $O(n\log n)$ quartets.

The $O(n\log n)$ query count is asymptotically optimal, since there are $2^{\Omega(n\log n)}$ such networks and each quarnet carries $O(1)$ bits.

## Depends on

- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](../../../coalescent-theory/multispecies-coalescent/tree-of-blobs-identifiability/blob-and-tree-of-blobs-of-a-phylogenetic-network.md)

## Expansion

Leaves are inserted one at a time into a growing canonical form. To place a new leaf $x$, the algorithm walks a balanced decomposition of the current network: at each cut-edge $uv$ with split $A \mid B$, a constant number of quarnet-splits $a_1x \mid b_1b_2$ (with $a_1, b_1$ and a distinguishing set of the blob containing $v$) decides on which side $x$ belongs, so each insertion costs $O(\log n)$ queries, in the spirit of binary search for trees. Within a cycle, four-cycle quarnets locate the attachment point and the reticulation. Quarnets are the natural input because they are identifiable from sequence data under standard network models, whereas the full network is not inferred directly.

## Sources

- Martin Frohn, Niels Holtgrefe, Leo van Iersel, Mark Jones and Steven Kelk, "Reconstructing semi-directed level-1 networks using few quarnets", Journal of Computer and System Sciences 152 (2025), 103655, <https://doi.org/10.1016/j.jcss.2025.103655>; numbering as in arXiv:2409.06034: lemma on splits (Section 3) and main theorems of Sections 3–5.
