# Negative-weight SSSP, minimum cycle mean and strong directed LDD in O((m + n log log n) log^2 n log(nW)) time

Let $G$ be a directed graph with $n$ vertices, $m$ edges, integer weights $w(e)\ge -W$ (with $W\ge 0$ least possible, and $\log W$ read as $\max\{1,\log W\}$), and source $s$. There are Las Vegas algorithms, each running in time $O((m+n\log\log n)\log^2 n\log(nW))$ with high probability and in expectation, that

1. either compute a shortest-path tree from $s$ or find a negative cycle in $G$;
2. compute $\mathrm{dist}_G(s,v)\in\mathbb{Z}\cup\{\pm\infty\}$ for all $v$, even when negative cycles exist;
3. find a cycle $C$ minimizing the mean weight $w(C)/|C|$.

Moreover, there is a strong directed low-diameter decomposition with overhead $O(\log^3 n)$ computable in time $O((m+n\log\log n)\log^2 n)$ with high probability.

## Proof sketch

Restricted SSSP is solved in $O((m+n\log\log n)\log^2 n)$ by recursive decomposition. If the minimum weight exceeds $-3k$, rounding $w(e)$ to $\lceil w(e)/k\rceil+1$ produces a restricted graph whose distances, multiplied by $k$, give a price function making the minimum weight exceed $-2k$; with $k=\lfloor W/3\rfloor$ and $W\ge 24$ this raises the most negative weight from $-W$ to at least $-\frac34 W$, and merging this scaling with probability boosting costs only an $O(\log(nW))$ factor overall. Negative cycles are found by solving the Threshold problem, the least additive shift removing all negative cycles, with a noisy-binary-search procedure analysed by drift analysis; minimum cycle mean follows by Lawler's reduction, which Karp's $O(mn)$ characterization previously handled only in strongly polynomial time.

## Depends on

- [Minimum cycle mean of a weighted edge list](../minimum-cycle-mean/is-min-cycle-mean.md)
- [Negative-weight single-source shortest paths with integer weights bounded below by -W](negative-weight-sssp-integer-weights.md)
- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Proof depends on

- [Decomposition of restricted graphs: progress in size or kappa with O(log n) expected hits per shortest path](bcf-restricted-graph-decomposition.md)
- [Negative-weight SSSP in O(m log^8 n log W) time by a combinatorial Las Vegas algorithm](bnw-near-linear-negative-sssp.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
- Richard M. Karp, "A characterization of the minimum cycle mean in a digraph", Discrete Mathematics 23(3) (1978).
