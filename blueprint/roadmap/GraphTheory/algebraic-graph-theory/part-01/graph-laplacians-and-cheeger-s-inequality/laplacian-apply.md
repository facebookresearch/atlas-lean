# Entries of the weighted Laplacian

Let $V$ be a set, $E$ a finite set, and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to \mathbb{R}$. For all $u, v \in V$, the entries of the [Laplacian](laplacian.md) are

$$L_{u v} = \sum_{e \in E} w_e\, B_{u e}\, B_{v e},$$

where $B$ is the oriented incidence matrix, $B_{x e} = [x = e^-] - [x = e^+]$.
