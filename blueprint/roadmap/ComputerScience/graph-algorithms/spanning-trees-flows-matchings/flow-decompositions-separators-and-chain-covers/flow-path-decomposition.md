# Path decomposition of integral flows

Let $f$ be a feasible integral $s$-$t$ flow of value $k$ in a network $N$ with $s \ne t$. Then there are $k$ simple $s$-$t$ paths $P_1, \dots, P_k$, each using only arcs with positive flow, such that every arc $(u, v)$ lies on at most $f(u, v)$ of them. (The remainder $f - \sum_i \chi_{P_i}$ is a circulation.)

## Proof sketch

Cancel antiparallel flow, then repeatedly follow positive-flow arcs from $s$; conservation guarantees reaching $t$ or closing a cycle, and removing a found path lowers the value by one.

## Depends on

- [Feasible flow](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/is-feasible-flow.md)
- [Flow value](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/flow-value.md)

## Sources

- L. R. Ford Jr. and D. R. Fulkerson, "Flows in Networks", Princeton University Press, 1962.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
