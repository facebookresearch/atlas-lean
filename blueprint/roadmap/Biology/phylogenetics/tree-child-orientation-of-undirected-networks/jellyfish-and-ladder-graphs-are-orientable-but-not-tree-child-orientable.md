# Jellyfish and ladder graphs: orientable but not tree-child orientable

**Setting.** Undirected binary phylogenetic networks, orientations and tree-child orientability are as in the companion article. The **jellyfish graph** $J_k$ ($k\ge1$) is an undirected binary phylogenetic network on $X=\{x_1,\dots,x_k\}$ with $2k+6$ vertices and $2k+9$ edges in which the neighbors $x'_1,\dots,x'_k$ of the leaves form a path $x'_1\cdots x'_k$ whose two ends attach to a fixed six-vertex gadget; its cycle rank is $4$. The **ladder graph** $L_k$ is the undirected binary network on $X=\{a,b,c,d\}$ with vertices $t_i,b_i$ ($1\le i\le k+1$), paths $a\,t_1\cdots t_{k+1}\,c$ and $b\,b_1\cdots b_{k+1}\,d$, and rungs $t_ib_i$ joining the two rails so that every non-leaf vertex has degree $3$; its cycle rank $|E|-|V|+1$ is $k$.

**Theorem.**

1. In every orientation of $J_k$ at most one of the leaf neighbors $x'_1,\dots,x'_k$ is a reticulation, and $J_k$ is orientable but **not** tree-child orientable for every $k\ge1$.
2. $L_k$ is tree-child orientable if and only if $k\le3$. For $k\ge4$, a tree-child orientable network can be obtained from $L_k$ by subdividing edges and attaching exactly $k-3$ new leaves, and not with $k-4$ or fewer; an explicit linear-time placement achieves $k-3$.

## Depends on

- [Necessary conditions for tree-child orientability of undirected binary networks](necessary-conditions-for-tree-child-orientability.md)

## Expansion

For $J_k$, every orientation has exactly four reticulations (the cycle rank). Wherever the root is placed, all root-to-leaf paths enter the leaf-neighbor path through one of its two ends, so choosing one $x'_i$ as reticulation forces the directions of the path edges and makes every other $x'_j$ a tree vertex with out-degree $2$. A case analysis over the at most one reticulation on the path, and over root positions (never between two reticulations), always produces two adjacent reticulations or a tree vertex with two reticulation children, which tree-child networks forbid. For the ladder, the edge bound $|E|\le5|X|-6$ applied to $L_k$ with $m$ added leaves (cycle rank still $k$, $|X|=4+m$, so $|E|=2|X|+3k-3$) gives $3k\le3|X|-3$, i.e. $k\le m+3$, so at least $k-3$ leaves are needed. The construction roots at the rung $t_{k-2}b_{k-2}$, alternates the added leaves between the two rails, designates $k$ reticulations so that no two are adjacent or siblings, and invokes the uniqueness of the orientation given the root edge and in-degrees.

## Sources

- S. Maeda, Y. Kaneko, H. Muramatsu, Y. Murakami, M. Hayamizu, "Orienting undirected phylogenetic networks to tree-child networks", arXiv:2305.10162 (2023), Section 5: Lemma 13, Theorem 14 (jellyfish graphs), Theorem 15 (ladder graphs), <https://doi.org/10.48550/arXiv.2305.10162>.
