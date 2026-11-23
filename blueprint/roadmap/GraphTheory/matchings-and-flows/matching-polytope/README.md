# Matching polytope

For a finite graph $G = (V, E)$, the matching polytope is the convex hull in $\mathbb{R}^E$ of the incidence vectors of the matchings of $G$, and the perfect matching polytope that of the perfect matchings. For bipartite graphs nonnegativity and the degree constraints suffice; in general Edmonds (1965) showed that one more family is needed, an inequality for every odd set of vertices, since the vector $\tfrac12$ on the edges of a triangle satisfies the degree constraints. Edmonds' description came out of his weighted matching algorithm and is the prototype of polyhedral combinatorics: it gives a min-max formula for maximum-weight matchings by linear programming duality, and since the odd-set constraints can be separated in polynomial time (Padberg and Rao), the ellipsoid method optimises over the matching polytope although it has exponentially many facets.

- [Incidence vector of a subgraph's edges](edge-incidence.md)
- [Matching polytope](matching-polytope.md)
- [Perfect matching polytope](perfect-matching-polytope.md)
- [Edmonds' perfect matching polytope theorem](perfect-matching-polytope-eq.md)
- [Edmonds' matching polytope theorem](matching-polytope-eq.md)

## Related topics

- [Kőnig's theorem](../k-nig-s-theorem/README.md): the bipartite case, where the degree constraints already describe the matching polytope.
- [Total dual integrality](../../../Geometry/convex-geometry/total-dual-integrality/README.md): Edmonds' system is totally dual integral (Cunningham–Marsh), so its integrality also follows from the Edmonds–Giles theorem.
- [Ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/README.md): with a polynomial separation routine for the odd-set constraints, it optimises over the matching polytope in polynomial time.
