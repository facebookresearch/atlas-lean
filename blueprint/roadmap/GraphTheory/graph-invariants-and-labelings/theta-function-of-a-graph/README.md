# Theta function of a graph

The Lovász theta function $\vartheta(G)$ is defined by orthogonal labelings (orthonormal representations): vectors $a_v$, one per vertex, with $a_u \perp a_v$ whenever $u \ne v$ are not adjacent. Relative to a nonzero handle $c$, the cost of $a_v$ is the squared cosine $\langle c, a_v\rangle^2 / (\lVert c\rVert^2 \lVert a_v\rVert^2)$, and $\vartheta(G)$ is the infimum of the reals $t \ge 0$ with $t \cdot \mathrm{cost}(a_v) \ge 1$ at every vertex for some labeling and handle; for a finite graph with at least one vertex this is the least possible value of $\max_v 1/\mathrm{cost}(a_v)$ over labelings of positive cost at every vertex. Two pieces of linear algebra give Lovász's sandwich theorem $\alpha(G) \le \vartheta(G) \le \chi(\bar G)$: Bessel's inequality bounds the total cost of a stable set by $1$, and a cover of the vertices by $k$ cliques yields a labeling all of whose costs are $1/k$. On perfect graphs the sandwich collapses, so $\vartheta(G) = \alpha(G)$. Grötschel, Lovász and Schrijver showed that $\vartheta$ can be computed in polynomial time with the ellipsoid method, which gives polynomial algorithms for stable sets, cliques and colourings in perfect graphs; $\vartheta$ also has characterisations by eigenvalues and semidefinite duality. The theta body $\mathrm{TH}(G)$ of Grötschel, Lovász and Schrijver lies between the stable set polytope and the clique-constrained polytope; $\vartheta(G)$ is the maximum of $\sum_v x_v$ over it, and $\mathrm{STAB}(G) = \mathrm{QSTAB}(G)$ exactly for perfect graphs.

- [Orthogonal labeling of a graph](is-orthogonal-labeling.md)
- [Cost of a vector in an orthogonal labeling](cost.md)
- [Costs are nonnegative](cost-nonneg.md)
- [Stable sets have total cost at most one](sum-cost-le-one.md)
- [Feasible values of the theta program](theta-feasible.md)
- [Labelings in any finite-dimensional space give feasible values](mem-theta-feasible-of-finite-dimensional.md)
- [Every feasible value dominates the independence number](indep-num-le-of-mem-theta-feasible.md)
- [Lovász theta function](lovasz-theta.md)
- [Theta is nonnegative](lovasz-theta-nonneg.md)
- [A colouring of the complement gives a feasible theta value](nat-cast-mem-theta-feasible-of-colorable.md)
- [Theta is bounded by the clique cover number](lovasz-theta-le-of-colorable.md)
- [Independence number is at most theta](indep-num-le-lovasz-theta.md)
- [Theta is at most the chromatic number of the complement](lovasz-theta-le-chromatic-number-compl.md)
- [Lovász's sandwich theorem](sandwich.md)
- [Theta equals the independence number on perfect graphs](lovasz-theta-eq-indep-num-of-is-perfect.md)
- [Characteristic vector of a vertex set](char-vec.md)
- [Stable set polytope](stab.md)
- [Clique-constrained stable set polytope](qstab.md)
- [Theta body](th.md)
- [The theta body is convex](convex-th.md)
- [Stable sets lie in the theta body](char-vec-mem-th.md)
- [The stable set polytope lies in the theta body](stab-subset-th.md)
- [The theta body lies in the clique-constrained polytope](th-subset-qstab.md)
- [Knuth's sandwich of convex sets](stab-subset-th-subset-qstab.md)
- [Theta is the maximum of the coordinate sum over the theta body](lovasz-theta-eq-s-sup-th.md)
- [Perfect graphs are those with STAB = QSTAB](is-perfect-iff-stab-eq-qstab.md)

## Related topics

- [Shannon capacity of a graph](../shannon-capacity-of-a-graph/README.md): Lovász introduced $\vartheta$ to bound the Shannon capacity; his bound gives the capacity $\sqrt 5$ of the pentagon.
- [Perfect graphs](../../graph-coloring/part-01/perfect-graphs/README.md): the graphs on which $\alpha(G) = \vartheta(G) = \chi(\bar G)$.
- [Fractional coloring](../../graph-coloring/part-01/fractional-coloring/README.md): Knuth's $\kappa(G) = \max\{\mathbf 1 \cdot x : x \in \mathrm{QSTAB}(G)\}$, by LP duality the fractional chromatic number of $\bar G$, also lies between $\vartheta(G)$ and $\chi(\bar G)$ (Knuth, eq. (4.9)).
- [Ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/README.md): the algorithm through which $\vartheta$, and hence $\alpha$ and $\chi$ of perfect graphs, are computed in polynomial time.
- [Goemans–Williamson MAX-CUT algorithm](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/README.md): the other basic semidefinite
  relaxation of a combinatorial problem, with vectors attached to vertices, rounded by a random
  hyperplane.
