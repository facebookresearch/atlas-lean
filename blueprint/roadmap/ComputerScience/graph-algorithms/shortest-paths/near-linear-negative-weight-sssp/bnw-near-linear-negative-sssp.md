# Negative-weight SSSP in O(m log^8 n log W) time by a combinatorial Las Vegas algorithm

There is a randomized Las Vegas algorithm that, given a directed graph $G$ with $n$ vertices, $m$ edges and integer weights $w(e)\ge -W$ ($W\ge 2$), and a source $s$, either returns a shortest-path tree from $s$ or returns a cycle of negative weight. Its running time is $O(m\log^8 n\log W)$ with high probability and in expectation. The algorithm is combinatorial: besides the low-diameter decomposition it uses only Dijkstra's algorithm, Bellman-Ford relaxations, strongly connected components and topological sorting. For comparison, Johnson's reweighting approach needs one full Bellman-Ford run, $O(mn)$ time, before Dijkstra's algorithm applies.

## Proof sketch

Goldberg's bit-scaling framework reduces the problem to $O(\log W)$ instances with all weights at least $-1$, and splitting each vertex into a zero-weight cycle makes all out-degrees constant with $O(m)$ vertices and edges. On such an instance, SPmain multiplies all weights by $2n$, sets $B$ to $2n$ rounded up to a power of $2$, and makes $\log_2 B = O(\log n)$ calls to ScaleDown with $\Delta=n$ and $B$ halving down to $1$; the resulting price function leaves all weights at least $-1$, and Dijkstra's algorithm on the reduced weights plus $1$ returns a shortest-path tree, in expected $O(m\log^5 n)$ time when no negative cycle exists (and SPmain never terminates otherwise). Running $O(\log n)$ time-capped copies gives a Monte Carlo algorithm, and a Lawler-style search for the smallest additive shift that removes all negative cycles, at a further $O(\log^2 n)$ factor, converts it into a Las Vegas algorithm that also outputs a negative cycle.

## Depends on

- [Negative-weight single-source shortest paths with integer weights bounded below by -W](negative-weight-sssp-integer-weights.md)
- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Proof depends on

- [ScaleDown: halving the most negative weight in expected O(m log^3 n log Delta) time](scaledown-recursive-scaling.md)
- [A feasible price function exists exactly when the graph has no negative cycle](feasible-potential-iff-no-negative-cycle.md)
- [ElimNeg: the Dijkstra-Bellman-Ford hybrid runs in time proportional to the negative-edge counts of shortest paths](elimneg-dijkstra-bellman-ford-hybrid.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
- Andrew V. Goldberg, "Scaling Algorithms for the Shortest Paths Problem", SIAM Journal on Computing 24(3) (1995).
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022).
