# Minimum perfect matchings on even vertex sets cost at most half a tour

Let $d$ be a symmetric cost with the triangle inequality, let $\tau$ be a closed walk visiting every vertex, and let $O$ be a set of an even number of vertices. Then a minimum-weight perfect matching $M$ on $O$ satisfies $2\, d(M) \le d(\tau)$.

## Proof sketch

Shortcut $\tau$ to a cycle through $O$ only; its edges split into two perfect matchings on $O$ by alternation, and the cheaper one costs at most half.

## Depends on

- [Symmetric TSP as a decision problem](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/traveling-salesperson-problem/tsp-dec.md)
- [Perfect matching](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/perfect-matching.md)

## Sources

- N. Christofides, "Worst-Case Analysis of a New Heuristic for the Travelling Salesman Problem", technical report 388, Graduate School of Industrial Administration, Carnegie-Mellon University, 1976.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
