# Christofides' 3/2-approximation for metric TSP

**Christofides' algorithm**: compute a minimum spanning tree $T$ of the complete graph, a minimum-weight perfect matching $M$ on the vertices of odd degree in $T$ (there are evenly many by the handshake lemma), an Euler circuit of the multigraph $T \uplus M$, and shortcut repeated vertices. For every symmetric cost with the triangle inequality the resulting tour costs at most $\frac32$ times the cost of any Hamiltonian cycle, in particular of an optimal tour.

## Proof sketch

$d(T) \le \mathrm{OPT}$ since deleting an edge of an optimal tour gives a spanning tree; $d(M) \le \mathrm{OPT}/2$ by the matching bound; the Euler circuit costs $d(T) + d(M)$ and shortcutting does not increase cost.

## Depends on

- [Symmetric TSP as a decision problem](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/traveling-salesperson-problem/tsp-dec.md)
- [The APPROX-TSP-TOUR algorithm](../double-tree-approximation-for-metric-tsp/approx-tsptour.md)

## Proof depends on

- [Minimum perfect matchings on even vertex sets cost at most half a tour](tsp-perfect-matching-bound.md)
- [A minimum spanning tree costs at most any tour](../double-tree-approximation-for-metric-tsp/weight-le-tour-cost.md)
- [Euler circuits in connected even graphs](../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/exists-is-eulerian.md)
- [Handshake lemma for edge-indexed multigraphs](../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/even-sum-degree.md)

## Sources

- N. Christofides, "Worst-Case Analysis of a New Heuristic for the Travelling Salesman Problem", technical report 388, Graduate School of Industrial Administration, Carnegie-Mellon University, 1976.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
