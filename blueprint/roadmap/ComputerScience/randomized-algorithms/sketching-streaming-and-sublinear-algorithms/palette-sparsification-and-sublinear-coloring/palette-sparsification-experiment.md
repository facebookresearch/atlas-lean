# Palette sparsification experiment, sampled lists and the conflict graph

Let $G = (V, E)$ be a simple undirected graph with $n$ vertices and maximum degree $\Delta$. Given palettes $\Pi(v)$ (for $(\Delta + 1)$-coloring, $\Pi(v) = \{1, \dots, \Delta + 1\}$ for all $v$) and list sizes $\ell : V \to \mathbb{N}$, the *palette sparsification experiment* samples, independently for every $v \in V$, a uniformly random subset $L(v) \subseteq \Pi(v)$ of size $\min(\ell(v), |\Pi(v)|)$. An *$L$-coloring* is a map $\chi$ with $\chi(v) \in L(v)$ for all $v$ and $\chi(u) \ne \chi(v)$ for all $\{u, v\} \in E$. The *conflict graph* is

$$
G_L = \big(V, \{\{u, v\} \in E : L(u) \cap L(v) \ne \emptyset\}\big).
$$

Since an edge whose endpoints share no sampled color is never monochromatic under an $L$-coloring, $\chi$ is an $L$-coloring of $G$ if and only if it is an $L$-coloring of $G_L$; algorithms therefore only need $G_L$.

## Depends on

- [The LIST COLORING decision problem](../../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/list-coloring/list-coloring-dec.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
- Sepehr Assadi, Helia Yazdanyar, "Simple Sublinear Algorithms for (Delta+1) Vertex Coloring via Asymmetric Palette Sparsification", SOSA (2025); TheoretiCS 5 (2026), Article 3, arXiv:2502.17629.
