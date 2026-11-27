# Karger's skeleton: logarithmically many trees one of which 2-respects the minimum cut

There is a randomized algorithm that, given a connected undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and positive weights, computes in $O(m + n \log^3 n)$ time a family of $O(\log n)$ spanning trees of $G$ such that, with probability at least $1 - n^{-c}$, every fixed global minimum cut of $G$ $2$-respects at least one tree of the family.

## Proof sketch

Sample edges (with weights treated as multiplicities) at a rate making the minimum cut of the sampled skeleton $H$ equal to $\Theta(\log n)$; by Chernoff bounds and the bound on the number of approximately minimum cuts, every cut of $H$ is within a factor $1 \pm \varepsilon$ of its scaled weight in $G$ with high probability. A greedy packing of $O(\log n)$ trees in $H$ has value close to $\lambda(H)/2$, so the minimum cut of $G$, which is a near-minimum cut of $H$, $2$-respects a constant fraction of the packing by the counting lemma. Sampling $O(\log n)$ trees from the packing proportionally to weight yields the family.

## Depends on

- [Cuts that k-respect a spanning tree](cuts-k-respecting-a-spanning-tree.md)
- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [A near-maximum tree packing has many trees that 2-respect a minimum cut](tree-packing-two-respects-minimum-cut.md)
- [Fixed-direction Chernoff bound](../../../../../Probability/large-deviations/cram-r-s-theorem/cramer-upper-bound.md)
- [At most $n(n-1)/2$ minimum cuts](../../../../randomized-algorithms/karger-s-algorithm/two-mul-length-min-cuts-le.md)

## Sources

- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
