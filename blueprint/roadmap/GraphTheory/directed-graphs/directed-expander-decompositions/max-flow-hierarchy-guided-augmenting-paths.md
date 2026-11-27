# Exact maximum flow in n^{2+o(1)} log U time by augmenting paths guided by a directed expander hierarchy

There is a randomized combinatorial algorithm that, given a directed $n$-vertex simple graph with integer edge capacities in $\{1,\dots,U\}$ and vertices $s,t$, computes an exact maximum $s$-$t$ flow with high probability in $n^{2+o(1)}\log U$ time. The algorithm is an implementation of the augmenting-path framework: augmenting paths are listed by a weighted push-relabel algorithm whose edge weights are $w(u,v)=|\tau(u)-\tau(v)|$ for a topological vertex order $\tau$ respecting a $1/n^{o(1)}$-expander hierarchy. This improves the long-standing bound $O(m\min\{m^{1/2},n^{2/3}\})$ of earlier augmenting-path algorithms (Karzanov, Even-Tarjan, Goldberg-Rao) whenever $m=\omega(n^{4/3})$.

## Proof sketch

Given a $\phi$-expander hierarchy $\mathcal{H}$ of height $\eta$, every feasible integral flow $f$ can be rerouted into a feasible flow $f'$ with $|f'|\ge|f|/(\eta+1)$ whose total weight under $w_{\mathcal{H}}$ is at most $|f'|\cdot O(n\eta^2\log n/\phi)$; this uses a length-congestion tradeoff for rerouting flow inside expanders, level by level. Weighted push-relabel with this weight function and a matching label bound therefore returns an $O(\log n)$-approximate maximum flow in $\tilde O(n^2/\phi)$ time. After capacity scaling, which costs an $O(\log U)$ factor, the algorithm rebuilds a $1/n^{o(1)}$-expander hierarchy of height $O(\log n)$ on the current residual graph in $n^{2+o(1)}$ time and repeats on the residual instance; $O(\log^2 n)$ such rounds exhaust the maximum flow. Robustness of the hierarchy under flow augmentation is what keeps its construction within $n^{2+o(1)}$ time.

## Depends on

- [Directed phi-expander hierarchies of a directed graph](directed-phi-expander-hierarchy.md)
- [Feasible flow](../../matchings-and-flows/max-flow-min-cut-theorem/is-feasible-flow.md)
- [Flow value](../../matchings-and-flows/max-flow-min-cut-theorem/flow-value.md)

## Proof depends on

- [Directed expander hierarchies of logarithmic height exist and can be constructed in n^{2+o(1)} time](directed-expander-hierarchy-existence-construction.md)
- [Directed phi-expanders are strongly connected and route terminal demands with congestion O(log n / phi)](directed-expander-connectivity-and-routing.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Sources

- Aaron Bernstein, Joakim Blikstad, Thatchaphol Saranurak, Ta-Wei Tu, "Maximum Flow by Augmenting Paths in n^(2+o(1)) Time", FOCS (2024), arXiv:2406.03648.
