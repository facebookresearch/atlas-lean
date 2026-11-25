# Erdős–Stone theorem

Turán's theorem determines the largest number of edges of a graph on $n$ vertices without $K_{r+1}$: it is the number $t(n, r) = (1 - 1/r + o(1))\, n^2/2$ of edges of the Turán graph $T(n, r)$. The Erdős–Stone theorem (1946) shows that $\varepsilon n^2$ more edges force much more than a $K_{r+1}$: they force the complete $(r+1)$-partite graph $K_{r+1}(t)$ with $t$ vertices in each class, for every fixed $t$ and $n$ large. Bollobás and Erdős (1973), and Bollobás, Erdős and Simonovits (1976), showed that $t$ can grow like $\log n / \log(1/\varepsilon)$, and that this order in $n$ is best possible.

Every graph $H$ of chromatic number $r + 1$ lies in $K_{r+1}(t)$ for $t = |V(H)|$, and lies in no $r$-partite graph. So Erdős–Stone gives the Turán density of every graph with at least one edge,

$$\pi(H) = 1 - \frac{1}{\chi(H) - 1},$$

the Erdős–Simonovits corollary. For bipartite $H$ it only says $\mathrm{ex}(n, H) = o(n^2)$, and the [Kővári–Sós–Turán bound](../kovari-sos-turan.md) gives an explicit upper bound for $K_{s,t}$.

The edge form of the Erdős–Stone theorem follows from its minimum-degree form by deleting vertices of small degree. It gives the upper bound in the density formula; the lower bound comes from the $r$-colourability of Turán graphs.

- [Erdős–Stone theorem](eventually-complete-equipartite-graph-is.md)
- [Turán density of a general graph (Erdős–Stone–Simonovits)](turan-density-eq-one-sub-inv-of-chromati.md)
- [Turán density of complete multipartite graphs](turan-density-complete-equipartite-graph.md)
- [Deletion of low-degree vertices](exists-subset-forall-le-deg-in.md)
- [Lower bound on the Turán density, chromatic form](one-sub-inv-le-turan-density-of-chromati.md)
- [Lower bound on the Turán density](one-sub-inv-le-turan-density.md)
- [Extremal numbers dominate those of cliques](extremal-number-top-le.md)
- [Turán graphs are $r$-colourable](turan-graph-colorable.md)
- [Degree inside a vertex set](deg-in.md)
- [Ordered adjacent pairs inside a vertex set](adj-pairs-in.md)

## Related topics

- [Turán density of complete graphs](../tur-n-density-of-complete-graphs/README.md): the case $H = K_{r+1}$, proved, which the general formula reduces to.
- [Turán numbers of bipartite graphs](../tur-n-numbers-of-bipartite-graphs/README.md): the degenerate case $\chi(H) = 2$, where the Erdős–Stone theorem only gives $o(n^2)$.
- [Triangle density and flag algebras](../triangle-density-and-flag-algebras/README.md): Razborov's flag-algebra method, which goes beyond the existence of a copy of $H$ to the minimum density of triangles above the Mantel threshold.
- [Graph limits](../../random-graphs/graph-limits/README.md): Lovász's graphons and homomorphism densities, the analytic setting in which extremal densities such as $\pi(H)$ are studied as limits.
