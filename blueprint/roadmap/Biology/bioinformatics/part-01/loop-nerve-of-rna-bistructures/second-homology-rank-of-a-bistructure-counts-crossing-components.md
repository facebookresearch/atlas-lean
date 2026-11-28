# Second homology rank of a bistructure counts crossing components

**Setting.** A *bistructure* $B(R,S)$ is a pair of RNA secondary structures $R$ and $S$ (noncrossing arc diagrams) on the same backbone of $n$ vertices; sequences compatible with both are *bicompatible*. Each structure decomposes into loops (hairpin, interior, multi- and exterior loops), and each loop is regarded as its set of vertices. Let $B = \{L_1, \dots, L_m\}$ be all loops of $R$ and of $S$. The *loop nerve* is the simplicial complex

$$K(B) = \dot{\bigcup_{d \ge 0}} K_d(B), \qquad \{L_{i_0}, \dots, L_{i_d}\} \in K_d(B) \iff \bigcap_{k=0}^d L_{i_k} \ne \varnothing,$$

with topological realization $T(B)$. It has no simplices of dimension above $3$, and its only nontrivial homology groups are $H_0(T(B)) \cong \mathbb{Z}$ and $H_2(T(B))$, free abelian of rank $r_2(B)$.

An $R$-arc $(i,j)$ and an $S$-arc $(r,s)$ *cross* if $i < r < j < s$. The *line graph* of $B$ has the arcs as vertices and an edge between crossing arcs; a *crossing component* is the arc set of a connected component of the line graph with more than one vertex.

**Theorem.** If the bistructure $B(R,S)$ has $r$ crossing components, then

$$r_2(B) = r.$$

More precisely, the closure of the substructure induced by a crossing component realizes a hollow sphere, contributing exactly $1$ to the rank of $H_2$; and if $B$ has no crossing arcs and no overlaps (vertices of degree four), then $H_2 = 0$ and the graph on $2$-simplices of the loop nerve, joined when they share an edge, is a tree.

## Expansion

Overlaps, where an $R$-arc and an $S$-arc share an endpoint, correspond to filled tetrahedra; splitting such a vertex into two adjacent vertices without creating a crossing removes one edge of the tetrahedron and leaves $r_2$ unchanged, so one may assume there are none. Without crossings the loops of $R$ and $S$ intersect in a tree-like pattern of ribbons and filled pieces with no $2$-cycles. Each crossing component produces one enclosed $2$-cycle. Algorithmically, Boltzmann sampling of bicompatible sequences under a full loop energy model works by removing loops in some order; for $r_2(B) = 0$ an explicit loop-removal order minimizes the resulting dynamic-programming complexity, while all hardness comes from resolving the spheres, which is done locally by cutting one $S$-arc per crossing component.

## Sources

- F. W. Huang, C. L. Barrett and C. M. Reidys, "The energy-spectrum of bicompatible sequences", arXiv:1910.00190 (2019), Materials and Methods: loop nerve, overlaps and crossing components, Lemma 1, Lemma 2, Theorem 1 and Lemma 3, <https://doi.org/10.48550/arXiv.1910.00190>.
