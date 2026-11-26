# Negative-weight SSSP, minimum cycle mean and strong directed LDD in O((m + n log log n) log^2 n log(nW)) time

Let $G$ be a directed graph with $n$ vertices, $m$ edges, integer weights $w(e)\ge -W$, and source $s$. There are Las Vegas algorithms, each running in time $O((m+n\log\log n)\log^2 n\log(nW))$ with high probability and in expectation, that

1. either compute a shortest-path tree from $s$ or find a negative cycle in $G$;
2. compute $\mathrm{dist}_G(s,v)\in\mathbb{Z}\cup\{\pm\infty\}$ for all $v$, even when negative cycles exist;
3. find a cycle $C$ minimizing the mean weight $w(C)/|C|$.

Moreover, there is a strong directed low-diameter decomposition with overhead $O(\log^3 n)$ computable in time $O((m+n\log\log n)\log^2 n)$ with high probability.

## Proof sketch

Restricted SSSP is solved in $O((m+n\log\log n)\log^2 n)$ by recursive decomposition. Rounding $w(e)$ to $\lceil 3w(e)/(W+1)\rceil+1$ produces a restricted graph whose distances yield a price function reducing the most negative weight from $-W$ to $-\frac34 W$, and merging this scaling with probability boosting costs only an $O(\log(nW))$ factor overall. Negative cycles are found by solving the Threshold problem, the least additive shift removing all negative cycles, with a noisy-binary-search procedure analysed by drift analysis; minimum cycle mean follows by Lawler's reduction, which Karp's $O(mn)$ characterization previously handled only in strongly polynomial time.

## Depends on

- [Decomposition of restricted graphs: progress in size or kappa with O(log n) expected hits per shortest path](bcf-restricted-graph-decomposition.md)
- [Negative-weight SSSP in O(m log^8 n log W) time by a combinatorial Las Vegas algorithm](bnw-near-linear-negative-sssp.md)
- [Karp's minimum cycle mean theorem](../minimum-cycle-mean/karp-min-cycle-mean.md)
- [Minimum cycle mean of a weighted edge list](../minimum-cycle-mean/is-min-cycle-mean.md)

## Proof depends on

- [Decomposition of restricted graphs: progress in size or kappa with O(log n) expected hits per shortest path](bcf-restricted-graph-decomposition.md)
- [Negative-weight SSSP in O(m log^8 n log W) time by a combinatorial Las Vegas algorithm](bnw-near-linear-negative-sssp.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
- Richard M. Karp, "A characterization of the minimum cycle mean in a digraph", Discrete Mathematics 23(3) (1978).
