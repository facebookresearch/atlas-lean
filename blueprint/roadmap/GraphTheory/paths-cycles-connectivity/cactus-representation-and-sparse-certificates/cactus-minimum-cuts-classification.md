# Minimum cuts of a weighted cactus are tree edges or pairs of edges on one cycle

Let $H$ be a cactus with at least two nodes, carrying its $\lambda$-weighting. Then $\lambda(H) = \lambda$, and a node set $X$ with $\emptyset \ne X \subsetneq V(H)$ is a side of a minimum cut of $H$ if and only if $\partial X$ consists of exactly one tree edge, or of exactly two edges lying on a common cycle. Consequently the number of minimum cuts of $H$ (counted as unordered bipartitions) is

$$
t + \sum_{\text{cycles } Z} \binom{|Z|}{2},
$$

where $t$ is the number of tree edges and $|Z|$ the length of the cycle $Z$.

## Proof sketch

Contract every cycle to a node: the result is a tree whose edges are the tree edges of $H$. A cut $X$ crosses any cycle in an even number of edges, so $w(\partial X) = \lambda \cdot (\#\text{tree edges in } \partial X) + \tfrac{\lambda}{2} \sum_Z |\partial X \cap E(Z)|$, where each nonzero summand $|\partial X \cap E(Z)|$ is at least $2$. Since $X$ is a proper nonempty subset of a connected graph, $\partial X$ is nonempty, so $w(\partial X) \ge \lambda$, with equality exactly when $\partial X$ is one tree edge or two edges of one cycle. Each tree edge and each pair of edges on one cycle determines a distinct bipartition, which gives the count.

## Depends on

- [Weighted cactus graphs with tree edges and cycle edges](weighted-cactus-graph.md)
- [Steiner minimum cuts of a terminal set](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Sources

- Efim A. Dinits, Alexander V. Karzanov, Michael V. Lomonosov, "On the Structure of a System of Minimum Edge Cuts of a Graph", Studies in Discrete Optimization (1976).
