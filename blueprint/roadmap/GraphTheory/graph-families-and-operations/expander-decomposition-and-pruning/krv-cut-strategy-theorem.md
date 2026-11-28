# Random-projection cut strategies win the cut-matching game in O(log^2 n) rounds

There is a randomized polynomial-time cut-player strategy that in each round finds a bisection $(S, \bar{S})$ such that adding any perfect matching between $S$ and $\bar{S}$ reduces a random-walk potential, in expectation, by a factor $1 - \Omega(1/\log n)$. Consequently, whatever perfect matchings across the chosen bisections the matching player adds, after $T = O(\log^2 n)$ rounds of the cut-matching game the matchings form a mixing sequence with high probability, and their union, the $T$-regular multigraph $H_T$ (each edge weighted by the number of matchings containing it), has edge expansion $h(H_T) \ge 1/2$.

Consequently, for an undirected graph $G$ with $n$ vertices and $m$ edges, the sparsest cut (edge expansion) of $G$ can be approximated within a factor $O(\log^2 n)$ by a randomized algorithm running in time $\tilde O(m + n^{3/2})$, using $O(\log^2 n)$ single-commodity maximum flow computations as its only flow primitive.

## Proof sketch

The cut player maintains the random-walk matrix of $H_t$ (each matching averages the walk distributions of matched vertices) and projects the rows onto a random direction; it bisects the vertices by the median of the projections. A potential, the total squared distance of the walk distributions from uniform, drops by a $1 - \Omega(1/\log n)$ factor per round in expectation whenever the matching player's matching crosses the chosen bisection, so after $O(\log^2 n)$ rounds the walk mixes: from every start the walk reaches every vertex with probability at least $1/(2n)$, which gives $H_T$ edge expansion at least $1/2$. In the algorithm, each matching is found as a flow of value $n/2$ across the bisection with congestion $1/\alpha$; if the flow fails, max-flow min-cut yields a cut of expansion below $\alpha$, and otherwise $H_T$ embeds in $G$ with congestion $T/\alpha$, certifying $h(G) \ge \Omega(\alpha/T)$.

## Depends on

- [The Khandekar-Rao-Vazirani cut-matching game](krv-cut-matching-game.md)

## Proof depends on

- [Max-flow min-cut theorem](../../matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Cut capacity](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/cut-capacity.md)

## Sources

- Rohit Khandekar, Satish Rao, Umesh Vazirani, "Graph Partitioning using Single Commodity Flows", STOC (2006), authors' copy, abstract, Theorem 2.1 and Section 3 (mixing sequences, the bisection step with expected potential drop $1 - \Omega(1/\log n)$, and $O(\log^2 n)$ iterations); J. ACM 56(4) (2009).
- Lorenzo Orecchia, Leonard J. Schulman, Umesh V. Vazirani, Nisheeth K. Vishnoi, "On Partitioning Graphs via Single Commodity Flows", STOC (2008).
