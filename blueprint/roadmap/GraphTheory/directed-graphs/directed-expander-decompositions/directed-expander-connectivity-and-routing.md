# Directed phi-expanders are strongly connected and route terminal demands with congestion O(log n / phi)

Let $G=(V,E)$ be a directed unweighted multigraph on $n$ vertices and $0<\phi\le 1$.

1. If every vertex has positive degree and $G$ is a $\phi$-expander, then $G$ is strongly connected.
2. If $G$ is strongly connected and a $\phi$-expander with respect to $F\subseteq E$, with $1/\phi\le\mathrm{poly}(m)$, then for every supply $\Delta$ and demand $\nabla$ on $V$ with $\|\Delta\|_1=\|\nabla\|_1$, $\Delta(v)\le\deg_F(v)$ and $\nabla(v)\le\deg_F(v)$ for all $v$, there is a flow $f$ in $G$ routing $\Delta$ to $\nabla$ with $f(e)=O(\log m/\phi)$ on every edge and $\sum_{e\in F}f(e)\le|f|\cdot O(\log m/\phi)$, so that flow paths use $O(\log m/\phi)$ edges of $F$ on average.

The bounds in item 2 depend on $m$, not on $n$: in a multigraph $m$ need not be polynomial in $n$, and a long bidirected path whose edge multiplicities grow exponentially has constant conductance while every path between its ends has $n-1$ edges. When $m\le\mathrm{poly}(n)$ the bounds read $O(\log n/\phi)$.

## Proof sketch

For item 1, if $G$ is not strongly connected, let $S$ be the union of a source component of the condensation; then $E(\bar S,S)=\emptyset$ while $\mathrm{vol}(S),\mathrm{vol}(\bar S)>0$ by the positive-degree assumption, so $S$ is $\phi$-sparse. For item 2, by max-flow min-cut the demand is routable with congestion $1/\phi$ because every cut carries at least $\phi$ times the terminal volume of its smaller side in each direction. Shortening paths uses the expansion repeatedly: balls grown in terminal volume from any vertex at least multiply by $(1+\phi)$ per $O(1)$ terminal edges until they contain half the terminal volume, so, as the terminal volume is at most $2m$, $O(\log m/\phi)$ terminal edges suffice to connect any terminal pair, and decomposing the routing with this length bound costs an extra $O(\log m)$ factor in congestion.

## Depends on

- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)
- [Strongly connected vertices](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md)

## Proof depends on

- [Edmonds-Karp computes a maximum flow and a minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)
- [Acyclic condensation](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/condensation-acyclic.md)

## Sources

- Aaron Bernstein, Joakim Blikstad, Thatchaphol Saranurak, Ta-Wei Tu, "Maximum Flow by Augmenting Paths in n^(2+o(1)) Time", FOCS (2024), arXiv:2406.03648.
- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
