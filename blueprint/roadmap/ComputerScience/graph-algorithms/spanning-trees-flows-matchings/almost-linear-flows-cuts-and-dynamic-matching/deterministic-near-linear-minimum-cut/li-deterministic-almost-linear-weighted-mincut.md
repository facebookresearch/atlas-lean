# Deterministic almost-linear minimum cut in weighted graphs (Li)

There is a deterministic algorithm that computes a global minimum cut of a connected undirected graph with $n$ vertices, $m$ edges and polynomially bounded positive weights (all in $[n^{-O(1)}, n^{O(1)}]$) in $m^{1+o(1)}$ time. Along the way it deterministically constructs a family of $n^{o(1)}$ spanning trees one of which $2$-respects a global minimum cut.

## Proof sketch

The only randomized step of Karger's algorithm is the sampled skeleton. Li derandomizes the Benczur-Karger style sampling by the method of pessimistic estimators: an expander decomposition hierarchy supplies a small family of potential functions that dominate the failure probability of all cuts simultaneously, so that the sample can be fixed edge by edge while keeping every approximately minimum cut well approximated. The skeleton has minimum cut $n^{o(1)}$ and preserves the minimum cut of $G$ up to a factor $7/6$, so Karger's deterministic tree packing on it gives $n^{o(1)}$ trees one of which $2$-respects the minimum cut, and the deterministic $2$-respecting cut algorithm is applied to each.

## Depends on

- [Cuts that k-respect a spanning tree](cuts-k-respecting-a-spanning-tree.md)
- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [Karger's skeleton: logarithmically many trees one of which 2-respects the minimum cut](karger-skeleton-tree-family.md)
- [Minimum 2-respecting cut of a spanning tree in O(m log n) deterministic time](minimum-two-respecting-cut-algorithm.md)
- [A near-maximum tree packing has many trees that 2-respect a minimum cut](tree-packing-two-respects-minimum-cut.md)
- [Weighted expander decompositions with volumes measured in the host graph](expander-decomposition.md)

## Sources

- Jason Li, "Deterministic Mincut in Almost-Linear Time", STOC (2021), arXiv:2106.05513.
- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
