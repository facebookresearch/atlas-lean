# Triangle density and flag algebras

How few triangles can a graph with a given edge density have? Write $n$ for the number of vertices, $m$ for the number of edges and $T$ for the number of triangles. [Goodman's bound](goodman.md) $3nT \ge m(4m - n^2)$ is proved by summing the [common neighbourhood bound](degree-add-degree-le.md) $|N(u) \cap N(v)| \ge \deg u + \deg v - n$ over the ordered pairs $(u, v)$ of adjacent vertices, whose common-neighbour counts add up to the number of [ordered triangles](ordered-triangles.md), and applying Cauchy–Schwarz to the degrees ([ordered form](goodman-ordered-triangles-nat.md), [homomorphism-count form](goodman-ordered-triangles.md)). With no triangles it gives [Mantel's theorem](four-mul-card-edge-finset-le-sq-of-cliqu.md), $4m \le n^2$.

The objects of Razborov's flag algebras are [induced densities](induced-density.md): $p(H, G)$ is the probability that a random $|H|$-subset of the vertices of $G$ induces a copy of $H$. Their basic identity is [averaging](induced-density-eq-average.md): for $|H| \le l \le |G|$, $p(H, G)$ is the average of the [densities inside](induced-density-in.md) the $l$-subsets of vertices, a [double count](sum-card-filter-powerset-card.md) of $k$-sets inside $l$-sets. Grouping the $l$-subsets by the isomorphism type $F$ of the graph they induce gives the chain rule $p(H, G) = \sum_F p(H, F)\,p(F, G)$, so that inequalities between finitely many densities, proved once for all graphs on $l$ vertices, hold for every large graph; flag-algebra proofs combine such identities with Cauchy–Schwarz inequalities.

In the language of graph limits, Goodman's bound says $t(K_3) \ge \rho(2\rho - 1)$ for homomorphism densities, and Razborov's flag-algebra calculus derives it as the inequality $K_3 \ge \rho(2\rho - 1)$ (*Flag algebras*, J. Symbolic Logic 72 (2007), Example 11 in the author's version). The bound is tight only at the edge densities $1 - 1/t$ of balanced complete multipartite graphs. The exact asymptotic minimum is [Razborov's function](razborov-triangle-density.md) $h(a)$, the triangle density of complete $(t+1)$-partite graphs with $t$ equal large parts; it [vanishes up to density $1/2$](razborov-triangle-density-of-le-half.md) and [equals $t(t-1)/(t+1)^2$ at the Turán densities](razborov-triangle-density-one-sub-inv.md). [Razborov's minimum triangle density theorem](razborov-minimum-triangle-density.md) (2008), one of the first major applications of flag algebras, shows that no graph does better.

The finite statements use homomorphism-count normalisations ($n^2$, $n^3$). The induced-density form $T/\binom{n}{3} \ge \rho(2\rho - 1)$ with $\rho = m/\binom{n}{2}$ holds only as $n \to \infty$; the four-cycle violates it.

- [Induced density](induced-density.md)
- [Induced copies of $H$ inside a vertex set](induced-count-in.md)
- [Induced density of H inside a vertex set](induced-density-in.md)
- [Number of $l$-supersets of a $k$-set](card-superset-powerset-card.md)
- [Double counting $k$-sets inside $l$-sets](sum-card-filter-powerset-card.md)
- [Averaging identity for induced densities](induced-density-eq-average.md)
- [Ordered triangles of a graph](ordered-triangles.md)
- [Membership in the ordered triangles](mem-ordered-triangles.md)
- [Ordered triangles through common neighbourhoods](card-ordered-triangles.md)
- [Ordered triangles and triangles](card-ordered-triangles-eq-six-mul.md)
- [Common neighbourhood bound](degree-add-degree-le.md)
- [Goodman's bound for ordered triangles](goodman-ordered-triangles-nat.md)
- [Goodman's bound in homomorphism-count form](goodman-ordered-triangles.md)
- [Goodman's bound on the number of triangles](goodman.md)
- [Mantel's theorem from Goodman's bound](four-mul-card-edge-finset-le-sq-of-cliqu.md)
- [Razborov's triangle density function](razborov-triangle-density.md)
- [Razborov's function vanishes up to edge density one half](razborov-triangle-density-of-le-half.md)
- [Razborov's function at the Turán densities](razborov-triangle-density-one-sub-inv.md)
- [Razborov's minimum triangle density theorem](razborov-minimum-triangle-density.md)
- [Homomorphism density inequalities](homomorphism-density-inequalities/README.md)

## Related topics

- [Turán density of complete graphs](../tur-n-density-of-complete-graphs/README.md): $\pi(K_{r+1}) = 1 - 1/r$, of which Mantel's theorem is the case $r = 2$.
- [Pentagons in triangle-free graphs](../pentagons-in-triangle-free-graphs/README.md): Erdős's pentagon problem, settled with flag algebras by Grzesik and by Hatami, Hladký, Kráľ, Norine and Razborov.
- [Finitely forcible graphons](../../random-graphs/finitely-forcible-graphons/README.md): graphons and subgraph densities, the limit objects on which flag-algebra inequalities such as $K_3 \ge \rho(2\rho - 1)$ are statements.
- [Maximal cliques and triangles](../../independence-and-domination/maximal-cliques-and-triangles/README.md): triangles through a given edge, the local quantity summed in Goodman's argument.
- [Threshold for triangles](../../random-graphs/threshold-for-triangles/README.md): triangles in the random graph $G(n, p)$, whose triangle density is about $p^3$, against the minimum over all graphs of edge density $p$ studied here.
- [Gowers uniformity norms](../../../Combinatorics/additive-combinatorics/progressions-dense-sets/gowers-uniformity-norms/README.md): cube densities in abelian groups, whose positivity and Gowers–Cauchy–Schwarz inequality come, like flag-algebra inequalities, from averaging identities and Cauchy–Schwarz.
