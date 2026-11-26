# Maximum number of trees displayed by a tree-child network

**Definitions.** A (binary) phylogenetic network on $X$ is a rooted acyclic digraph without parallel arcs whose root has out-degree two, whose out-degree-zero vertices are exactly the leaves $X$ (each of in-degree one), and whose other vertices are tree vertices (in-degree one, out-degree two) or reticulations (in-degree two, out-degree one). It is tree-child if every non-leaf vertex is the parent of a tree vertex or a leaf. $\mathcal N$ displays a rooted binary phylogenetic $X$-tree $\mathcal T$ if a subdivision of $\mathcal T$ is obtained from $\mathcal N$ by deleting vertices and arcs; $T(\mathcal N)$ is the set of displayed trees, up to isomorphism. $\{a,b\}$ is a reticulated cherry if the parent of $b$ is a reticulation and the parent of $a$ is one of its parents.

**Facts.** A tree-child network with $n$ leaves has at most $n-1$ reticulations. An embedding uses at most one of the two reticulation arcs into each reticulation, so a network with $k$ reticulations has $|T(\mathcal N)|\le 2^k$.

**Theorem.** For every binary tree-child network $\mathcal N$ with $n\ge2$ leaves,
$$|T(\mathcal N)|\le 2^{n-1}-1,$$
and the bound is attained for every $n\ge2$. If $|T(\mathcal N)|=2^{n-1}-1$, then $\mathcal N$ has $n-1$ reticulations and exactly one tree in $T(\mathcal N)$ is displayed twice; this tree is the one obtained from $\mathcal N$ by repeatedly replacing a reticulated cherry with a cherry (deleting the reticulation arc not from the cherry partner) until a tree remains.

## Expansion

With $k\le n-1$ reticulations there are at most $2^k\le2^{n-1}$ ways to choose one incoming arc per reticulation, so the content of the theorem is that, when $k=n-1$, two of these choices always yield the same tree. The proof inducts on $n$ using the cherry or reticulated cherry that every tree-child network has, and the fact that deleting a reticulation arc of a tree-child network leaves a tree-child network. Sharpness is shown by an explicit family of tree-child networks attaining $2^{n-1}-1$ for every $n\ge2$.

## Sources

- Y. Murakami, C. Semple, "Note on the Maximum Number of Trees Displayed by a Tree-Child Network", arXiv:2606.14464 (2026), Theorem 1.1, Proposition 2.1, Proposition 3.2, <https://doi.org/10.48550/arXiv.2606.14464>.
