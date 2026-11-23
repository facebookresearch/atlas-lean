# Primal–dual method for constrained forests

Goemans and Williamson (*SIAM J. Comput.* 24(2) (1995)) give one approximation algorithm for a
whole class of network design problems: find a minimum-cost edge set meeting every cut
$\delta(S)$ with $f(S) = 1$, for a proper function $f$. Steiner trees, Steiner forests
(generalized Steiner trees), $T$-joins, shortest paths and spanning trees are examples. The
algorithm grows dual variables on the components that still need an edge, adds an edge when a
dual constraint becomes tight, and finally deletes unneeded edges; its cost is at most
$2 - 2/|A|$ times the dual value (Theorem 2.4), so the integrality gap of the cut relaxation is
at most $2 - 2/|A|$.

The algorithm runs in $O(\min(n^2 \log n, mn\,\alpha(m, n)))$ time, and the later sections of the
paper extend it (for example §4, where the algorithm also returns a vertex set).

- [Edges of a cut](cut-edges.md)
- [Proper requirement function](is-proper.md)
- [Steiner forest requirement](steiner-forest-requirement.md)
- [Goemans–Williamson integrality gap for proper constrained forest problems](exists-forest-cost-le-of-lp-feasible.md)

## Related topics

- [Weighted vertex cover by the pricing method](../weighted-vertex-cover-by-the-pricing-method/README.md):
  the primal–dual (pricing) method on its simplest example.
- [Linear programming](../../../Geometry/convex-geometry/linear-programming/README.md): the relaxation
  and its dual.
- [Steiner tree](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/README.md):
  NP-completeness of a special case.
