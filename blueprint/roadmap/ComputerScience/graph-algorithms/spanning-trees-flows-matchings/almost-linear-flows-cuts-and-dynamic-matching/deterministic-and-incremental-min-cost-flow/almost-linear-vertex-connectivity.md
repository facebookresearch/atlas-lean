# Vertex connectivity of undirected graphs in almost-linear time

There is a randomized algorithm that, given an undirected graph with $n$ vertices and $m$ edges, computes with high probability its vertex connectivity, that is the minimum number of vertices whose removal disconnects the graph or leaves a single vertex, together with a minimum vertex cut, in $m^{1+o(1)}$ time.

## Proof sketch

Vertex connectivity reduces to $\mathrm{polylog}(n)$ maximum flow computations on graphs with $O(m)$ edges in total plus $\widetilde{O}(m)$ additional work, so any $m^{a}$-time maximum flow algorithm with $a \ge 1$ gives an $\widetilde{O}(m^{a})$-time algorithm; each vertex-capacitated flow instance is turned into an edge-capacitated one by vertex splitting, and Menger's theorem identifies its value with a minimum vertex separator. Plugging in *Maximum flow in almost-linear time with a logarithmic dependence on capacities*, or its deterministic counterpart for the flow calls, yields $m^{1+o(1)}$; the randomness lies in the reduction's sampling of terminal sets.

## Proof depends on

- [Maximum flow in almost-linear time with a logarithmic dependence on capacities](../almost-linear-flow-interior-point-method/almost-linear-maximum-flow.md)
- [Menger's theorem, vertex form](../../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/menger-vertex.md)

## Sources

- Jason Li, Danupon Nanongkai, Debmalya Panigrahi, Thatchaphol Saranurak, Sorrachai Yingchareonthawornchai, "Vertex Connectivity in Poly-logarithmic Max-flows", STOC (2021), arXiv:2104.00104.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
