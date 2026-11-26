# Exact maximum flow in n^{2+o(1)} log U time by augmenting paths guided by a directed expander hierarchy

There is a randomized combinatorial algorithm that, given a directed $n$-vertex simple graph with integer edge capacities in $\{1,\dots,U\}$ and vertices $s,t$, computes an exact maximum $s$-$t$ flow with high probability in $n^{2+o(1)}\log U$ time. The algorithm is an implementation of the augmenting-path framework: augmenting paths are listed by a weighted push-relabel algorithm whose edge weights are $w(u,v)=|\tau(u)-\tau(v)|$ for a topological vertex order $\tau$ respecting a $1/n^{o(1)}$-expander hierarchy. Even for unit capacities this improves the combinatorial bound $O(m\min\{\sqrt m,n^{2/3}\})$ of Karzanov and Even-Tarjan whenever $m=\omega(n^{4/3})$.

## Proof sketch

Given a hierarchy, every feasible integral flow can be rerouted, with small congestion and length overhead, into a flow whose total weight under $w_{\mathcal{H}}$ is at most $n^{1+o(1)}$ times its value; this uses a new length-congestion tradeoff for rerouting flow inside expanders, level by level from the top of the hierarchy. Weighted push-relabel then runs in time proportional to the weight of an optimal short flow, so augmenting the maximum flow in $O(\log U)$ scaling phases costs $n^{2+o(1)}$ per phase. The hierarchy is constructed in $n^{2+o(1)}$ time and remains usable as the residual graph changes because reversing a whole augmenting path affects expander pruning about as much as a single edge update.

## Depends on

- [Directed expander hierarchies of logarithmic height exist and can be constructed in n^{2+o(1)} time](directed-expander-hierarchy-existence-construction.md)
- [Directed phi-expanders are strongly connected and route terminal demands with congestion O(log n / phi)](directed-expander-connectivity-and-routing.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Proof depends on

- [Directed expander hierarchies of logarithmic height exist and can be constructed in n^{2+o(1)} time](directed-expander-hierarchy-existence-construction.md)
- [Directed phi-expanders are strongly connected and route terminal demands with congestion O(log n / phi)](directed-expander-connectivity-and-routing.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Sources

- Aaron Bernstein, Joakim Blikstad, Thatchaphol Saranurak, Ta-Wei Tu, "Maximum Flow by Augmenting Paths in n^(2+o(1)) Time", FOCS (2024), arXiv:2406.03648.
