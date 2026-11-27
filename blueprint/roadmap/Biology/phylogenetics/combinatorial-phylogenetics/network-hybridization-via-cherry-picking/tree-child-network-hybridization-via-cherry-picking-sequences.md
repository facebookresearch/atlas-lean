# Tree-child network hybridization via cherry-picking sequences

**Definitions.** A rooted phylogenetic network on taxa $X$ is *tree-child* if every non-leaf node has a child that is not a reticulation. A pair of leaves $(x,y)$ is a *cherry* if $x,y$ share a parent, and a *reticulated cherry* if the parent of $x$ is a reticulation and the parent of $y$ is a parent of that reticulation; both are *reducible pairs*. Reducing $(x,y)$ deletes $x$ (cherry) or the reticulation edge into $x$'s parent (reticulated cherry) and suppresses degree-2 nodes. A **tree-child sequence** (TCS) is a sequence of ordered leaf pairs such that the second coordinate of each pair appears later as a first coordinate or as the second coordinate of the last pair, and no first coordinate is reused later as a second coordinate. Its weight is $w(S)=|S|-|X|+1$. A network $N$ *displays* $N'$ if $N'$ is obtained from $N$ by deleting reticulation edges, removing leaves, suppressing degree-2 nodes and contracting edges. **Tree-child Network Hybridization**: given a set $\mathcal N$ of tree-child networks, find a tree-child network displaying all of them with the minimum number $h_{\mathrm{tc}}(\mathcal N)$ of reticulations.

**Theorem.**

1. A set $\mathcal N$ of tree-child networks on $X$ is displayed by some tree-child network if and only if a single TCS reduces every network in $\mathcal N$; then $h_{\mathrm{tc}}(\mathcal N)$ equals the minimum weight of such a sequence.
2. Any TCS reducing a tree-child network $N$ contains every reticulated cherry $(x,y)$ of $N$; hence if $N_1$ has the reticulated cherry $(x,y)$ and $N_2$ has $(y,x)$, no tree-child network displays both.
3. If some tree-child network with at most $k$ reticulations displays $\mathcal N$, one can be found in time $O\big((8k)^k\cdot\mathrm{poly}(|X|,|\mathcal N|)\big)$; the problem is fixed-parameter tractable in $k$.

## Expansion

The network built from a TCS by adding pairs in reverse order is tree-child, its reticulation number equals the sequence weight, and it displays every network the sequence reduces, while a displaying tree-child network's own sequence also reduces every displayed network; this gives item 1. The algorithm branches on reducible pairs: pairs that are reducible in every network still containing $x$ ("trivial pairs") can be reduced first without loss, and once none remain, the total number of reducible pairs across $\mathcal N$ is at most $8k$ (extending the bound of $4k$ cherries for sets of trees). Each branching step picks one of at most $8k$ pairs and increases the weight, so the search tree has at most $(8k)^k$ leaves.

## Sources

- Remie Janssen, Mark Jones, Yukihiro Murakami, "Combining Networks using Cherry Picking Sequences", arXiv:1912.03999 (2019), Definitions 1–7, Lemmas 3–5 and 10, Theorem 1, <https://doi.org/10.48550/arXiv.1912.03999>.
