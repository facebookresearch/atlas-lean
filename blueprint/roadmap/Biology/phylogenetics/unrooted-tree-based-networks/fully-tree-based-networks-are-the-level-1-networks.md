# Fully tree-based networks are the level-1 networks

Let $N$ be an unrooted phylogenetic network on a finite set $X$ (a connected simple graph with all degrees $1$ or $3$ and leaf set $X$). Every such network contains subtrees whose leaf set is $X$, obtained by pruning a union of paths from one leaf to all others. Call $N$ **fully tree-based** if *every* subtree of $N$ with leaf set $X$ is a spanning tree of $N$ (a support tree). $N$ is **level-1** if at most one edge must be removed from each blob (maximal cut-edge-free subgraph) to obtain a tree, i.e. every blob is a single cycle.

**Theorem.** $N$ is fully tree-based if and only if $N$ is a level-1 network.

This is the unrooted analogue of the characterisation of rooted networks in which every embedded tree with full leaf set is a base-tree (the tree-child networks).

## Depends on

- [Level bound for unrooted tree-based networks](level-bound-for-unrooted-tree-based-networks.md)

## Expansion

If every blob is a cycle, the third edge at each cycle vertex is a cut-edge, and in a level-1 network the far side of every cut-edge contains a leaf (a leafless pendant piece would need a cycle all of whose vertices have further exits, which cannot terminate). A subtree with leaf set $X$ must therefore pass through every cycle vertex, and since it is acyclic it omits exactly one edge per cycle, so it is spanning. Conversely, if $N$ is not level-1, some simple blob of level at least $2$ contains a vertex $v$ that is not on any pendant edge. Starting from a support tree through $v$, one can delete the tree edges at $v$ and reconnect the resulting pieces through other blob edges without using $v$, producing a subtree with leaf set $X$ that avoids $v$; this subtree is not spanning, so $N$ is not fully tree-based.

## Sources

- A. Francis, K. T. Huber, V. Moulton, "Tree-based unrooted phylogenetic networks", *Bulletin of Mathematical Biology* (2018), Section 5 (Lemmas 5–6, Theorem 5), <https://doi.org/10.1007/s11538-017-0381-3> (PMC5790869).
