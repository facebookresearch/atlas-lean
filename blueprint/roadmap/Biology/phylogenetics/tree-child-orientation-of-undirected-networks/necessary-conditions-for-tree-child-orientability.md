# Necessary conditions for tree-child orientability of undirected binary networks

**Setting.** An *undirected binary phylogenetic network* $N=(V,E)$ on a leaf set $X$ ($|X|\ge2$) is a connected finite simple graph whose degree-1 vertices are exactly the leaves $X$ and whose other vertices have degree $3$. An *orientation* $\hat N$ of $N$ is obtained by subdividing one edge $e_\rho$ by a new root $\rho$ and directing all edges so that the result is a directed binary phylogenetic network: acyclic, root with out-degree $2$, leaves with in-degree $1$, and every other vertex either a tree vertex (in-degree $1$, out-degree $2$) or a reticulation (in-degree $2$, out-degree $1$). $\hat N$ is *tree-child* if every non-leaf vertex has a child that is a tree vertex or a leaf. $N$ is **tree-child orientable** if some orientation of it is tree-child. This is relevant because distance-based methods such as Neighbor-Net output undirected networks, while evolutionary interpretation needs a direction of gene flow.

**Theorem.**

1. *(Reticulation number.)* Every orientation of $N$ has exactly $|R|=|E|-|V|+1$ reticulations (the cycle rank of $N$).
2. *(Root placement.)* In any orientation, at least one child of the root is a tree vertex; equivalently, the root edge $e_\rho$ cannot join two vertices that both become reticulations.
3. *(Edge bound.)* If $N$ is tree-child orientable then $|E|\le5|X|-6$, and this bound is attained (e.g. by a network with $|X|=3$ and $9$ edges).
4. *(Short leaf pairs.)* If $N$ has no two leaves $x,x'$ at graph distance $d_N(x,x')\in\{2,3\}$, then $N$ is not tree-child orientable.

None of these conditions is sufficient.

## Expansion

Item 1 follows from the in-degree count $\sum_v\delta^-(v)=|E|+1$ required of any orientation. For item 3, an orientation adds one edge, a directed binary network with $r$ reticulations has $2|X|+3r-2$ arcs, and a tree-child network has $r\le|X|-1$; hence $|E|+1\le2|X|+3(|X|-1)-2$. Item 4 uses that every tree-child network with at least two leaves has a cherry (two leaves with a common parent, distance $2$) or a reticulated cherry (distance $3$, through one tree vertex and one reticulation). Item 2 comes from the degree-cut characterization of constrained orientability: two reticulations below the root would form a forbidden reticulation cut. Item 4 also guides where to place the root when searching for a tree-child orientation.

## Sources

- S. Maeda, Y. Kaneko, H. Muramatsu, Y. Murakami, M. Hayamizu, "Orienting undirected phylogenetic networks to tree-child networks", arXiv:2305.10162 (2023), Section 4: Lemma 8, Theorem 9, Propositions 10–12, and Theorem 3 (constrained orientation, after Huber et al.), <https://doi.org/10.48550/arXiv.2305.10162>.
