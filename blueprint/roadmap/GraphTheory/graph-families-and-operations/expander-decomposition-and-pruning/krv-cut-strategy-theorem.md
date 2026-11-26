# Random-projection cut strategies win the cut-matching game in O(log^2 n) rounds

There is a randomized polynomial-time cut-player strategy such that, against every matching player, after $T = O(\log^2 n)$ rounds of the cut-matching game the multigraph $H_T$ (which is $T$-regular) satisfies $h(H_T) = \Omega(1)$ with high probability.

Consequently, for an undirected graph $G$ with $n$ vertices and $m$ edges, the edge expansion (sparsest cut value) of $G$ can be approximated within a factor $O(\log^2 n)$ by a randomized algorithm running in time $\tilde O(m + n^{3/2})$, using single-commodity maximum flow computations as its only flow primitive.

## Proof sketch

The cut player maintains the random-walk matrix of $H_t$ (each matching averages the walk distributions of matched vertices) and projects the rows onto a random direction; it bisects the vertices by the median of the projections. A potential, the total squared distance of the walk distributions from uniform, drops by a $1 - \Omega(1/\log n)$ factor per round in expectation whenever the matching player's matching crosses the chosen bisection, so after $O(\log^2 n)$ rounds the walk mixes and $H_T$ has constant edge expansion. In the algorithm, each matching is found as a flow of value $n/2$ across the bisection with congestion $1/\alpha$; if the flow fails, max-flow min-cut yields a cut of expansion below $\alpha$, and otherwise $H_T$ embeds in $G$ with congestion $T/\alpha$, certifying $h(G) \ge \Omega(\alpha/T)$.

## Depends on

- [The Khandekar-Rao-Vazirani cut-matching game](krv-cut-matching-game.md)

## Proof depends on

- [Max-flow min-cut theorem](../../matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Cut capacity](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/cut-capacity.md)

## Sources

- Rohit Khandekar, Satish Rao, Umesh Vazirani, "Graph Partitioning using Single Commodity Flows", STOC (2006); J. ACM 56(4) (2009).
- Lorenzo Orecchia, Leonard J. Schulman, Umesh V. Vazirani, Nisheeth K. Vishnoi, "On Partitioning Graphs via Single Commodity Flows", STOC (2008).
