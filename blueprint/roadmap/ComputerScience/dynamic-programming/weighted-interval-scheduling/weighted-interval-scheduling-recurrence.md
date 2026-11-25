# Weighted interval scheduling by dynamic programming

Let intervals $[s_i, f_i)$ with $s_i \le f_i$ have weights $w_i \ge 0$, two intervals being compatible when they are disjoint. Zero-length intervals ($s_i = f_i$) are empty, compatible with every interval, and can all be taken; remove them and order the remaining intervals ($s_i < f_i$) by finish time, $f_1 \le \dots \le f_n$, and let $p(j)$ be the largest $i < j$ with $f_i \le s_j$ ($0$ if none). Then $\mathrm{OPT}(0) = 0$ and $\mathrm{OPT}(j) = \max(\mathrm{OPT}(j-1), w_j + \mathrm{OPT}(p(j)))$ is the maximum weight of a set of pairwise compatible intervals among the first $j$, and tracing back which term attains each maximum returns such a set. Sorting and computing all $p(j)$ by binary search take $O(n \log n)$ comparisons and the recurrence $O(n)$ further operations.

Proof. An optimal set for the first $j$ intervals either omits interval $j$ (value $\mathrm{OPT}(j-1)$) or contains it; then every other member finishes by $s_j$ (members finishing after $s_j$ and before $f_j$ would overlap interval $j$), so the rest is a compatible set among the first $p(j)$ intervals, and conversely any such set extends by interval $j$.

## Background

- [Correctness and optimality of earliest-finish interval scheduling](../../greedy-algorithms-and-matroids/interval-scheduling/interval-schedule-correct.md): the unweighted greedy algorithm.

## Sources

- J. Kleinberg and É. Tardos, *Algorithm Design*, Pearson, 2005; lecture slides by K. Wayne, §6.1 Weighted interval scheduling, <https://www.cs.princeton.edu/~wayne/kleinberg-tardos/pdf/06DynamicProgrammingI.pdf>
