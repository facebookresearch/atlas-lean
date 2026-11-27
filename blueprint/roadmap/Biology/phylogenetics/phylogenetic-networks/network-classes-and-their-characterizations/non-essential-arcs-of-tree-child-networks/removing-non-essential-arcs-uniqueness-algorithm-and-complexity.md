# Removing non-essential arcs from phylogenetic networks: uniqueness, algorithm and complexity

**Setting.** For a phylogenetic network $\mathcal{N}$ on $X$, an arc is non-essential if every rooted phylogenetic $X$-tree displayed by $\mathcal{N}$ has an embedding avoiding it. Deleting non-essential reticulation arcs shrinks the network, and with it the multiset of $2^k$ candidate embeddings ($k$ reticulations) that tree-based algorithms enumerate, without losing any displayed tree.

**Theorem (reduction count).** Let $\mathcal{N}$ be a tree-child network on $X$ and let

$$\mathcal{N} = \mathcal{N}_0, \mathcal{N}_1, \dots, \mathcal{N}_m = \mathcal{N}'$$

be tree-child networks with each $\mathcal{N}_{i+1}$ obtained from $\mathcal{N}_i$ by deleting a non-essential reticulation arc. If $\mathcal{N}'$ has no non-essential reticulation arc, then $\mathcal{N}$ has exactly $m$ tight caterpillar ladders, and $\mathcal{N}'$ is obtained from $\mathcal{N}$ by deleting either the first or the last rung of each tight caterpillar ladder of $\mathcal{N}$. In particular, every maximal reduction sequence has the same length.

**Theorem (algorithm).** From a tree-child network $\mathcal{N}$ on $X$ one can compute, in time $O(|X|^3)$, a tree-child network on $X$ with no non-essential arcs that displays exactly the same set of rooted phylogenetic $X$-trees as $\mathcal{N}$.

**Theorem (hardness).** For arbitrary phylogenetic networks, the problem NON-ESSENTIAL-ARC (given $\mathcal{N}$ and a reticulation arc $e$, is $e$ non-essential?) is $\Pi_2^P$-complete.

## Depends on

- [Non-essential reticulation arcs and tight caterpillar ladders](non-essential-reticulation-arcs-and-tight-caterpillar-ladders.md)

## Expansion

By the ladder characterization, the non-essential reticulation arcs of a tree-child network are precisely the first and last rungs of its tight caterpillar ladders. Distinct tight ladders interact only mildly: deleting an extreme rung of one ladder makes the other extreme rung of that ladder essential and leaves the other tight ladders tight, so each ladder contributes exactly one deletion. Tight ladders can be found by local search around reticulations, which gives the cubic-time algorithm. Without the tree-child property the characterization fails, and membership in $\Pi_2^P$ is immediate (for all displayed trees there exists an avoiding embedding); hardness follows by reduction from DISPLAY-SET-CONTAINMENT, deciding whether every tree displayed by one network is displayed by another.

## Sources

- Simone Linz and Charles Semple, "Non-essential arcs in phylogenetic networks", Journal of Computer and System Sciences 128 (2022), 1–17, <https://doi.org/10.1016/j.jcss.2022.02.005>; numbering as in arXiv:2107.07721: Theorems 5.4, 5.5 and 6.1.
