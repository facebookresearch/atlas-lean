# Negative-weight SSSP, minimum cycle mean and strong directed LDD in O((m + n log log n) log^2 n log(nW)) time

Let $G$ be a directed graph with $n$ vertices, $m$ edges, integer weights $w(e)\ge -W$ (with $W\ge 0$ least possible), and source $s$. Throughout, $\log(nW)$ is read as $\log(n\max\{W,2\})$, which is positive and defined also for $W\in\{0,1\}$ (the source writes $O(\log W)$ for $O(\max\{1,\log W\})$). There are Las Vegas algorithms, each running in time $O((m+n\log\log n)\log^2 n\log(nW))$ with high probability and in expectation, that

1. either compute a shortest-path tree from $s$ or find a negative cycle in $G$;
2. compute $\mathrm{dist}_G(s,v)\in\mathbb{Z}\cup\{\pm\infty\}$ for all $v$, even when negative cycles exist;
3. find a cycle $C$ minimizing the mean weight $w(C)/|C|$, or report that $G$ has no cycle; for this item $W$ must bound the magnitudes of all weights, $|w(e)|\le W$ for every edge, because Lawler's reduction (Algorithm 8) runs the shortest-path machinery on the weights $n^2w(e)-n^3L$, where $L$ is the largest weight, and these have magnitude up to $n^2|w(e)|+n^3|L|$, which a lower bound $-W$ alone does not control (even for $W=1$).

Moreover, there is a strong directed low-diameter decomposition with overhead $O(\log^3 n)$ computable in time $O((m+n\log\log n)\log^2 n)$ with high probability.

## Proof sketch

Restricted SSSP is solved in $O((m+n\log\log n)\log^2 n)$ by recursive decomposition. If $G$ has no negative cycle and its minimum weight exceeds $-3k$ for an integer $k\ge 1$, rounding $w(e)$ to $\lceil w(e)/k\rceil+1$ and adding a new source with weight-$0$ edges to all vertices produces a restricted graph whose distances from that source, multiplied by $k$, give a price function making the minimum weight exceed $-2k$; with $k=\lfloor W/3\rfloor+1$ and $W\ge 24$ this raises the most negative weight from $-W$ to above $-2k \ge -\frac23 W-2 \ge -\frac34 W$, and merging this scaling with probability boosting costs only an $O(\log(nW))$ factor overall. Negative cycles are found by solving the Threshold problem, the least additive shift removing all negative cycles, with a noisy-binary-search procedure analysed by drift analysis; minimum cycle mean follows by Lawler's reduction, whose shifted weights satisfy $|n^2w(e)-n^3L|\le 2n^3W$ when $|w(e)|\le W$, so the scaling factor stays $O(\log(nW))$, which Karp's $O(mn)$ characterization previously handled only in strongly polynomial time.

## Depends on

- [Minimum cycle mean of a weighted edge list](../minimum-cycle-mean/is-min-cycle-mean.md)
- [Negative-weight single-source shortest paths with integer weights bounded below by -W](negative-weight-sssp-integer-weights.md)
- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Proof depends on

- [Decomposition of restricted graphs: progress in size or kappa with O(log n) expected hits per shortest path](bcf-restricted-graph-decomposition.md)
- [Negative-weight SSSP in O(m log^8 n log W) time by a combinatorial Las Vegas algorithm](bnw-near-linear-negative-sssp.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279, Theorems 1–3, Algorithm 8 and Section 6.
- Richard M. Karp, "A characterization of the minimum cycle mean in a digraph", Discrete Mathematics 23(3) (1978).
