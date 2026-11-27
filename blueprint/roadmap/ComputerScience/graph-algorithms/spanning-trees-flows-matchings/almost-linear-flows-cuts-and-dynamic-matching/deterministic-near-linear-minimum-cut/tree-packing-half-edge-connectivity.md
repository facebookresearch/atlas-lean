# Spanning tree packings of value at least half the edge connectivity

For every connected undirected graph $G$ with positive weights, $\tau(G) \ge \lambda(G)/2$. For an unweighted multigraph with edge connectivity $\lambda$ there are at least $\lfloor \lambda / 2 \rfloor$ pairwise edge-disjoint spanning trees.

## Proof sketch

By the Nash-Williams-Tutte theorem (and its fractional form via matroid base packing), $\tau(G)$ equals the minimum over partitions $\mathcal{P}$ of $V$ into $|\mathcal{P}| \ge 2$ parts of $w(E(\mathcal{P}))/(|\mathcal{P}| - 1)$, where $E(\mathcal{P})$ is the set of edges between different parts. Each part $P$ has $w(\partial P) \ge \lambda$, and every inter-part edge is counted twice in $\sum_P w(\partial P)$, so $w(E(\mathcal{P})) \ge |\mathcal{P}| \lambda / 2 \ge (|\mathcal{P}| - 1)\lambda/2$. The integral statement follows from the integral version of the same theorem.

## Depends on

- [Fractional spanning tree packings and the packing value](fractional-spanning-tree-packing.md)
- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Sources

- Crispin St. J. A. Nash-Williams, "Edge-Disjoint Spanning Trees of Finite Graphs", Journal of the London Mathematical Society (1961).
- William T. Tutte, "On the Problem of Decomposing a Graph into n Connected Factors", Journal of the London Mathematical Society (1961).
- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
