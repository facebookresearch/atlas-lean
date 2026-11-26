# Finiteness of valid-arc-deletion proximity and OSOS subgraphs

**Setting.** Networks are binary directed phylogenetic networks on $X$. A *valid arc deletion* deletes one arc and suppresses its endpoints, provided the result is again a phylogenetic network (no unlabelled out-degree-0 vertex and no parallel arcs). For a class $\mathcal C \in \{\mathcal T, \mathcal{TC}, \mathcal{O}r, \mathcal{TB}\}$ (trees, tree-child, orchard, tree-based) let $A^*_{\mathcal C}(N)$ be the minimum number of valid arc deletions that turn $N$ into a member of $\mathcal C$, with $A^*_{\mathcal C}(N) = \infty$ if no such sequence exists.

**OSOS subgraph.** For a tree vertex $u$ above a reticulation $v$, the pair $uv$ *induces a one-source-one-sink (OSOS) subgraph* if every root-to-$v$ path contains $u$ and every path from $u$ to a leaf contains $v$. The subgraph is the set of vertices that are descendants of $u$ and ancestors of $v$; $N$ is *OSOS-free* if no pair induces one.

**Theorem.**
1. $A^*_{\mathcal T}(N) < \infty$ if and only if $N$ is OSOS-free.
2. If $N$ is OSOS-free then $A^*_{\mathcal C}(N) < \infty$ for every $\mathcal C \in \{\mathcal T, \mathcal{TC}, \mathcal{O}r, \mathcal{TB}\}$.
3. For $\mathcal C \in \{\mathcal T, \mathcal{TC}, \mathcal{O}r\}$, if $A^*_{\mathcal C}(N) < \infty$ then $N$ is OSOS-free. Hence for these three classes finiteness of the measure is equivalent to OSOS-freeness.
4. All pairs inducing a (minimal) OSOS subgraph of a network on $n$ vertices can be found in $O(n \log n)$ time.
5. Computing $A^*_{\mathcal{O}r}(N)$ is NP-hard.

## Depends on

- [Leaf-addition proximity to tree-child, orchard and tree-based networks](leaf-addition-proximity-to-tree-child-orchard-and-tree-based-networks.md)

## Expansion

Inside an OSOS subgraph all genetic material entering at $u$ leaves through $v$, so any valid deletion of an arc inside it either creates parallel arcs or an unlabelled sink; the block can never be dismantled into a tree. Conversely, without such a block one can always find a reticulation arc whose deletion is valid and reduces the number of reticulations, and induction reaches a tree (hence also a tree-child, orchard and tree-based network). Tree-based networks may keep a reticulation inside an OSOS block, which is why item 3 excludes $\mathcal{TB}$. The detection algorithm uses dominator trees (Lengauer–Tarjan) on $N$ and on its reverse: $u$ must dominate $v$ from the root and $v$ must post-dominate $u$ towards the leaves.

## Sources

- L. van Iersel, M. Jones, E. Julien, Y. Long, "Proximity Measures for Classes of Phylogenetic Networks", arXiv:2607.11325 (2026), Definitions 3.2 and 6.1, Theorems 6.7, 6.10 and 7.10, Corollaries 6.8 and 6.9, <https://doi.org/10.48550/arXiv.2607.11325>.
