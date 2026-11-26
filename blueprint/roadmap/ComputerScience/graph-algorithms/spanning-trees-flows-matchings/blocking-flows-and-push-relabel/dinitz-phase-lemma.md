# Dinitz phase lemma

If $g$ is a blocking flow of the level network $L_f$ and $f' = f + g$ (with cancellation of antiparallel flow), then the residual distance from $s$ to $t$ in $N_{f'}$ is strictly larger than in $N_f$. Consequently after $T$ phases of augmenting by blocking flows the residual distance of $t$ has grown by at least $T$, and at most $|V| - 1$ phases occur before $t$ becomes unreachable.

## Proof sketch

Arcs created in $N_{f'}$ go from level $i+1$ to level $i$, so residual distances do not decrease; an $s$-$t$ path of the old length would lie in $L_f$ and avoid every saturated arc, contradicting blocking.

## Depends on

- [Level networks and blocking flows](level-networks-and-blocking-flows.md)

## Sources

- E. A. Dinic, "Algorithm for Solution of a Problem of Maximum Flow in Networks with Power Estimation", Soviet Mathematics Doklady 11, 1970.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
