# Flow equivalence of Gomory-Hu trees

Let $T$ be a weighted Gomory-Hu tree of a symmetric submodular $f$. For all distinct $s, t \in V$,

$$
\lambda_f(s, t) = \min_{uv \in P_T(s,t)} \lambda_f(u, v),
$$

where $P_T(s,t)$ is the tree path from $s$ to $t$, and the side of the minimizing tree edge is a minimum $s$-$t$ cut. Consequently the function $\lambda_f$ takes at most $|V| - 1$ distinct values on pairs of distinct vertices; for a graph, minimum cut values equal maximum flow values, so all $\binom{n}{2}$ pairwise maximum flow values are encoded by $n - 1$ numbers.

## Proof sketch

"$\ge$": every $s$-$t$ cut separates the endpoints of some tree edge on the path, and the triangle inequality $\lambda(s,t) \ge \min(\lambda(s,u), \lambda(u,t))$ follows from symmetry. "$\le$": the side of each path edge is an $s$-$t$ cut.

## Depends on

- [Gomory-Hu trees](gomory-hu-tree.md)
- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)

## Proof depends on

- [Every symmetric submodular function has a Gomory-Hu tree](gomory-hu-existence.md)
- [Uncrossing minimum cuts of symmetric submodular functions](uncrossing-minimum-cuts.md)

## Sources

- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
