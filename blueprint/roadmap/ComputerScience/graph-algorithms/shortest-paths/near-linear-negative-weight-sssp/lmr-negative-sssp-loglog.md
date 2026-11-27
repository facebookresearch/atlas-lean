# Negative-weight SSSP in O((m + n log log n) log(nW) log n log log n) time

There is a randomized algorithm that, given a directed graph with $n$ vertices, $m$ edges, integer weights $w(e)\ge -W$ for an integer $W\ge 2$, an upper bound on the absolute value of every negative weight (also when there is none), and a source $s$, succeeds with high probability and either computes a shortest-path tree from $s$ or, if a negative cycle exists, outputs one, in time

$$
O\big((m+n\log\log n)\log(nW)\log n\log\log n\big).
$$

This improves the Bringmann-Cassis-Fischer bound by a factor of nearly $\log n$. Negative cycles are handled directly inside the recursive algorithm rather than by a separate noisy binary search.

## Proof sketch

Follow the Bringmann-Cassis-Fischer framework with the recursion parameter $\kappa$ replaced by weak diameter, and decompose with the specialized loss-$O(\log n\log\log n)$ directed LDD, which merges the per-level and recursion-depth logarithmic losses into one factor: each scaling phase halves the most negative weight, decomposes the graph, recursively fixes the strongly connected components, repairs inter-component edges by the acyclic-condensation step, and repairs the cut edges with the Dijkstra-Bellman-Ford hybrid, whose cost is proportional to the expected number of cut edges on shortest paths. With loss $O(\log n\log\log n)$ the per-phase cost becomes $O((m+n\log\log n)\log n\log\log n)$, and $O(\log(nW))$ scaling phases complete the bound.

## Depends on

- [Negative-weight single-source shortest paths with integer weights bounded below by -W](negative-weight-sssp-integer-weights.md)

## Proof depends on

- [Directed low-diameter decompositions with loss O(log n log log n)](near-optimal-directed-ldd-loss.md)
- [Negative-weight SSSP, minimum cycle mean and strong directed LDD in O((m + n log log n) log^2 n log(nW)) time](bcf-faster-negative-sssp.md)

## Sources

- Jason Li, Connor Mowry, Satish Rao, "Faster Negative-Weight Shortest Paths and Directed Low-Diameter Decompositions", SODA (2026), arXiv:2510.22721.
- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
