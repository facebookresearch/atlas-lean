# Combinatorics and geometry of the space of circular split networks

**Setting.** A split of a finite set $X$ of $n$ species is a bipartition $A|B$; a split system is **circular** if there is a circular ordering $\pi$ of $X$ such that every split cuts the circle into two arcs, i.e. corresponds to a diagonal or side of an $n$-gon labelled by $\pi$. A dissimilarity matrix is realized by a weighted circular split system if and only if it satisfies the **Kalmanson condition** for some circular ordering: for all $i < j < k < l$ in that ordering,

$$\delta(x_i,x_j) + \delta(x_k,x_l) \le \delta(x_i,x_k) + \delta(x_j,x_l), \qquad \delta(x_i,x_l) + \delta(x_j,x_k) \le \delta(x_i,x_k) + \delta(x_j,x_l),$$

generalizing the four-point condition for trees. The space $\mathcal{CSN}_n$ of metric circular split networks with $n$ labelled leaves is obtained by gluing one orthant $[0,\infty)^{n(n-3)/2}$ (coordinates = weights of the non-trivial splits, i.e. the diagonals of the labelled $n$-gon) for each of the $(n-1)!/2$ circular orderings up to rotation and reflection, identifying faces that represent the same split system. Normalizing total internal weight to $1$ gives the **network space** $\mathcal{N}_n$, analogous to the link of the origin in Billera–Holmes–Vogtmann tree space.

**Theorem.**

1. Let $\delta = 2^{n-1} - n - 1$ be the number of non-trivial splits of $X$. The fan $\mathcal{CSN}_n$ embeds naturally in $\mathbb{R}^{\delta}$ (one coordinate per non-trivial split, the split weight); each network has at most $n(n-3)/2$ non-zero coordinates.
2. $\mathcal{N}_n$ is a connected simplicial complex of dimension $n(n-3)/2 - 1$, with one $k$-simplex for every labelled $n$-gon with $k+1$ diagonals; $\mathcal{CSN}_n$ is not CAT(0).
3. For $n > 4$, $\mathcal{N}_n$ has $c = (n-1)!/2$ chambers of dimension $d = n(n-3)/2 - 1$, $c(d+1)$ ridges, $\delta$ vertices and $\binom{\delta}{2}$ edges; its $1$-skeleton is the complete graph on $\delta$ vertices.
4. Two chambers intersect in a face of dimension at most $(n-3)(n-2)/2 - 1$.
5. Two circular orderings are compatible with the same circular split system if and only if one polygonal representation can be turned into the other by a sequence of twists along noncrossing diagonals; using this, the real moduli space $\overline{\mathcal{M}}_0^n(\mathbb{R})$, tiled by $(n-1)!/2$ associahedra $K_{n-1}$, embeds into $\mathcal{N}_n$ via barycentric coordinates on the associahedra.

## Expansion

A circular split system is a set of diagonals of a labelled polygon, and the maximal ones are all diagonals of a fixed $n$-gon, giving $n(n-3)/2$ coordinates per chamber; different labellings up to dihedral symmetry give the chamber count. Any two splits of $X$ are simultaneously circular for some ordering, so every pair of vertices spans an edge, unlike tree space, where only compatible splits do. The failure of CAT(0) comes from short loops through chambers that share low-dimensional faces, so geodesics are not unique. The moduli-space embedding sends a face of an associahedron (a polygon with noncrossing diagonals) to the barycentric point whose coordinate on a diagonal $d$ is $1/(n-3)$ if $d$ is present, $0$ if $d$ crosses the face's diagonals, and a ratio of Catalan numbers otherwise; twists along diagonals glue the associahedra exactly as faces of $\mathcal{N}_n$ are glued.

## Sources

- Satyan L. Devadoss and Samantha Petti, "A Space of Phylogenetic Networks", arXiv:1607.06978 (2016), Theorems 2, 3, 7, 9 and 12, Propositions 4–6 and 13, Corollary 8, <https://doi.org/10.48550/arXiv.1607.06978>. Published version: SIAM Journal on Applied Algebra and Geometry 1 (2017) 683–705, <https://doi.org/10.1137/16M1103129>.
