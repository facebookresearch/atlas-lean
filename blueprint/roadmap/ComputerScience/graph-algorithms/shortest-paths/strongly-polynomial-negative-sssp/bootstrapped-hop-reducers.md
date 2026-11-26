# Bootstrapped hop reducers: real-weighted SSSP in O~(m n^{3/4} + m^{4/5} n) randomized time

The real-weighted SSSP problem on a directed graph with $n$ vertices and $m$ edges can be solved with high probability by a randomized algorithm in

$$
\tilde O\big(mn^{3/4}+m^{4/5}n\big)
$$

time; equivalently $\tilde O(mn^{3/4})$ when $m\ge n^{5/4}$ and $\tilde O(m^{4/5}n)$ when $m\le n^{5/4}$.

## Proof sketch

The framework of neutralizing remote sets and sandwiches is kept, but the layered hop-reducing auxiliary graph, whose size grows linearly with the hop reduction factor, is replaced by a bootstrapping process. Constant-hop reducers for small subgraphs of the input are built first and then iteratively amplified, composing reducers to multiply the hop reduction, and expanded to larger subgraphs, until a polynomial hop reduction over the whole graph is reached at near-linear size. Plugging the cheaper reducer into the remote-elimination step and rebalancing parameters yields the bound.

## Depends on

- [Real-weighted negative SSSP in the real RAM and strongly polynomial running time](real-weighted-sssp-strongly-polynomial.md)

## Proof depends on

- [Real-weighted SSSP in O(m n^{4/5} log^{2/5} n + n^{9/5} log^{7/5} n) randomized time via proper hop distances](hjq-mn-four-fifths.md)
- [r-hop reductions and the layered hop-reducing auxiliary graph](r-hop-reduction-auxiliary-graph.md)

## Sources

- Yufan Huang, Peter Jin, Kent Quanrud, "Faster negative length shortest paths by bootstrapping hop reducers", SODA (2026), arXiv:2506.00428.
