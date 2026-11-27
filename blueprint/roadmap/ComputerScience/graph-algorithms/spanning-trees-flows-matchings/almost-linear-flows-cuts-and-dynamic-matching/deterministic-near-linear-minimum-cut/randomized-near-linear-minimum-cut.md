# Randomized minimum cut of weighted graphs in O(m log^2 n) time

There is a randomized (Monte Carlo) algorithm that, given a connected undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and positive weights, outputs a cut that is a global minimum cut with probability at least $1 - n^{-c}$, in $O(m \log^2 n)$ time (Gawrychowski-Mozes-Weimann), improving Karger's $O(m \log^3 n)$ bound. Mukhopadhyay-Nanongkai give $O(m \log^2 n/\log\log n + n \log^6 n)$ by a different $2$-respecting procedure.

## Proof sketch

Compute Karger's skeleton family of $O(\log n)$ spanning trees, so that with high probability the minimum cut $2$-respects one of them. For each tree run the $O(m \log n)$ minimum $2$-respecting cut algorithm and return the best cut found. The total time is $O(\log n) \cdot O(m \log n) + O(m + n \log^3 n) = O(m \log^2 n)$.

## Depends on

- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [Karger's skeleton: logarithmically many trees one of which 2-respects the minimum cut](karger-skeleton-tree-family.md)
- [Minimum 2-respecting cut of a spanning tree in O(m log n) deterministic time](minimum-two-respecting-cut-algorithm.md)

## Sources

- Pawel Gawrychowski, Shay Mozes, Oren Weimann, "Minimum Cut in O(m log^2 n) Time", ICALP (2020), arXiv:1911.01145.
- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
- Sagnik Mukhopadhyay, Danupon Nanongkai, "Weighted Min-Cut: Sequential, Cut-Query and Streaming Algorithms", STOC (2020), arXiv:1911.01651.
