# Level networks and blocking flows

Let $N$ be a flow network with source $s$, sink $t$ and integral capacities, $f$ a feasible flow and $d(v)$ the residual distance (fewest arcs) from $s$ to $v$ in the residual network $N_f$. The **level network** $L_f$ consists of the residual arcs $u \to v$ with $d(v) = d(u) + 1$, with their residual capacities. A flow $g$ in $L_f$ is **blocking** if every $s$-$t$ path in $L_f$ contains an arc saturated by $g$.

## Depends on

- [Feasible flow](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/is-feasible-flow.md)
- [Cut capacity](../edmonds-karp-algorithm/cut-capacity.md)

## Sources

- E. A. Dinic, "Algorithm for Solution of a Problem of Maximum Flow in Networks with Power Estimation", Soviet Mathematics Doklady 11, 1970.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
