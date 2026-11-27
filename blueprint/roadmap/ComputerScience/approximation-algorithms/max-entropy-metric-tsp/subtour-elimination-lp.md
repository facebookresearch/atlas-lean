# Subtour elimination LP of a metric TSP instance

Let $(V,c)$ be a metric TSP instance with $n=|V| \ge 3$: $c$ is a symmetric nonnegative cost on the edge set $E$ of the complete graph on $V$ satisfying $c(uw) \le c(uv)+c(vw)$. Write $\delta(S)$ for the set of edges with exactly one endpoint in $S$. The subtour elimination LP (Held-Karp relaxation) is

$$
\mathrm{OPT}_{\mathrm{LP}}=\min\Big\{\sum_{e \in E} c_e x_e : x(\delta(v))=2\ \forall v \in V,\ x(\delta(S)) \ge 2\ \forall\, \emptyset \ne S \subsetneq V,\ x \ge 0\Big\}.
$$

The cut constraint for $S=\{u,v\}$ implies $x_{uv} \le 1$. The indicator vector of every Hamiltonian cycle is feasible, so $\mathrm{OPT}_{\mathrm{LP}} \le \mathrm{OPT}$, the minimum tour length. The LP is solvable in polynomial time by the ellipsoid method with a separation oracle (the equivalence of separation and optimization of Grötschel, Lovász and Schrijver): violated degree or nonnegativity constraints are found directly, and a violated cut constraint, if any, is found by a global minimum cut computation with capacities $x$.

## Depends on

- [Symmetric TSP instances](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/traveling-salesperson-problem/tsp-instance.md)
- [Length of a tour in the symmetric TSP](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/traveling-salesperson-problem/tour-length.md)
- [Cut capacity](../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/cut-capacity.md)

## Proof depends on

- [The ellipsoid method finds a point](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/ellipsoid-run-finds-point.md)
- [Stoer-Wagner in O(n^3) word-RAM time](../../graph-algorithms/spanning-trees-flows-matchings/deterministic-global-minimum-cuts/stoer-wagner-word-ram.md)
- [Grotschel-Lovasz-Schrijver equivalence of separation and optimization](../../../GraphTheory/graph-invariants-and-labelings/theta-sandwich-and-perfect-graph-optimization/separation-optimization-equivalence.md)

## Sources

- Michael Held, Richard M. Karp, "The Traveling-Salesman Problem and Minimum Spanning Trees", Operations Research (1970).
- Laurence A. Wolsey, "Heuristic Analysis, Linear Programming and Branch and Bound", Mathematical Programming Study 13 (1980).
- Martin Grötschel, László Lovász, Alexander Schrijver, "Geometric Algorithms and Combinatorial Optimization", Springer (1988).
