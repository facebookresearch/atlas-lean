# Homshifts

The homshift of a finite graph is the subshift of finite type of all graph homomorphisms from the grid $\mathbb{Z}^d$ into that graph.

Let $G$ be a finite undirected graph, possibly with self-loops, and $d \ge 1$. View $\mathbb{Z}^d$ as the grid graph, in which two points are adjacent when they differ by $1$ in exactly one coordinate. The *$d$-dimensional homshift* of $G$ is

$$
X^d_G = \{ x \in V_G^{\mathbb{Z}^d} : (x_{\mathbf{u}}, x_{\mathbf{v}}) \in E_G \text{ for all adjacent } \mathbf{u}, \mathbf{v} \in \mathbb{Z}^d \},
$$

the set of graph homomorphisms from the grid to $G$, with the shift action of $\mathbb{Z}^d$; it is a nearest-neighbor [subshift of finite type](subshifts-of-finite-type-on-groups.md) on $\mathbb{Z}^d$ whose constraint is the same in every direction. The homshift is transitive exactly when $G$ is connected, and topologically mixing exactly when $G$ is connected and not bipartite.

## Depends on

- [Subshifts of finite type on a finitely generated group](subshifts-of-finite-type-on-groups.md)

## Proof depends on

None.

## Expansion

Many properties of homshifts are decidable: a homshift is nonempty as soon as $G$ has an edge, a pattern extends to a full configuration if and only if it extends to a rectangle, and the topological entropy is computable from a description of the homshift.

## Sources

- N. Chandgotia, S. Gangloff, B. Hellouin de Menibus and P. Oprocha, "Undecidability of the block gluing classes of homshifts", Nonlinearity 39 (2026), no. 8, article 085011, https://doi.org/10.1088/1361-6544/ae73db; read in arXiv:2507.21342v2 (the introduction and the notation for homshifts in Section 2 of arXiv:2507.21342v2).
- N. Chandgotia, S. Gangloff, B. Hellouin de Menibus and P. Oprocha, "On the cohomology of homshifts", Transactions of the American Mathematical Society (2026), https://doi.org/10.1090/tran/9934; read in arXiv:2510.11969v3 (the definition of homshifts in Section 2 of arXiv:2510.11969v3).
