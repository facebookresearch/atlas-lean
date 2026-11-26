# Weighted interval scheduling by dynamic programming

Let intervals $1, \dots, n$ have start times $s_i$ and finish times $f_i$ in a linear order, with $s_i < f_i$, so that interval $i$ occupies the nonempty interval $[s_i, f_i)$, and weights $w_i$ in a linearly ordered commutative additive monoid with monotone addition, such as $\mathbb{N}$, $\mathbb{Z}$ or $\mathbb{R}$. Intervals $i$ and $k$ are compatible when $f_i \le s_k$ or $f_k \le s_i$; for intervals of positive length this says exactly that $[s_i, f_i)$ and $[s_k, f_k)$ are [disjoint](interval-compatible-iff-disjoint-ico.md). A set $S$ is an [optimal schedule](is-optimal-schedule.md) of the first $j$ intervals with value $v$ when $S \subseteq \{1, \dots, j\}$, any two distinct members of $S$ are compatible, $\sum_{i \in S} w_i = v$, and every set of pairwise compatible intervals among $1, \dots, j$ has total weight at most $v$.

Let [$p(j)$](wis-pred.md) be the largest $i$ with $1 \le i < j$ and $f_i \le s_j$, or $0$ if there is none. The [recurrence](wis-value.md) is $\mathrm{OPT}(0) = 0$ and $\mathrm{OPT}(j) = \max(\mathrm{OPT}(j-1), w_j + \mathrm{OPT}(p(j)))$ for $j \ge 1$, and its [traceback](wis-trace.md) is $T(0) = \emptyset$ and, for $j \ge 1$, $T(j) = \{j\} \cup T(p(j))$ if $\mathrm{OPT}(j-1) < w_j + \mathrm{OPT}(p(j))$ and $T(j) = T(j-1)$ otherwise.

**Theorem.**

1. If $f_1 \le \dots \le f_n$, then for every $j \le n$ the set $T(j)$ is an optimal schedule of the first $j$ intervals with value $\mathrm{OPT}(j)$. That is, $\mathrm{OPT}(j)$ is the maximum total weight of a set of pairwise compatible intervals among the first $j$, and tracing back which term attains each maximum returns such a set.
2. Whatever the order of the finish times, the [algorithm](wis-schedule.md) that sorts the intervals by finish time with merge sort, fills the table of the recurrence while computing each $p(j)$ by binary search, and traces back from $n$ returns an optimal schedule of the $n$ intervals together with its value.
3. The algorithm is charged one unit for each comparison of two finish times in the merge sort, for each comparison of a finish time with a start time in the binary searches, and for each comparison of two weights in the table and the traceback; nothing else is charged, so additions of weights, array and list operations and index arithmetic are free. Its cost is at most $2n\lceil \log_2 n \rceil + 2n$, where $n\lceil \log_2 n \rceil$ is read as $0$ when $n = 0$.

The source takes positive weights; here the weights need no sign condition, and the times may lie in any linear order. The hypothesis $s_i < f_i$ cannot be dropped: the intervals $[1, 1)$ and $[0, 1)$, in this order and both of weight $1$, have sorted finish times and are compatible, so the optimum is $2$, but $\mathrm{OPT}(2) = 1$. For natural weights, the value of an optimal schedule is the [brute-force optimum](eq-wis-opt.md) of the [exchange identity](../dynamic-programming-principles/weighted-interval-scheduling-exchange-identity.md).

**Proof.**

1. By induction on $j$; for $j = 0$ the empty set is the only candidate. Let $j \ge 1$. If $i < j$ is compatible with $j$, then $f_i \le s_j$, since $f_j \le s_i$ would give $s_i < f_i \le f_j \le s_i$; so $i \le p(j)$. Conversely, every $i$ with $1 \le i \le p(j)$ has $f_i \le f_{p(j)} \le s_j$. Hence a set of pairwise compatible intervals among the first $j$ either omits $j$, and then has weight at most $\mathrm{OPT}(j-1)$, or contains $j$, and then the rest is a compatible set among the first $p(j)$ intervals, so that, addition being monotone, its weight is at most $w_j + \mathrm{OPT}(p(j))$. The traceback takes the set of whichever term is larger, and adding $j$ to $T(p(j))$ keeps it compatible.
2. Merge sort returns a permutation $\sigma$ of $1, \dots, n$ with $f_{\sigma(1)} \le \dots \le f_{\sigma(n)}$, which the algorithm stores in an array. The binary search for $p(j)$ keeps $p(j)$ in its current range: it probes the middle index $m$ and, as the finish times are monotone, continues from $m$ upwards when $f_m \le s_j$ and below $m$ otherwise. So the table holds $\mathrm{OPT}$ and $p$ of the sorted intervals, and the traceback returns $T(n)$. Part 1 for the sorted intervals gives an optimal schedule of them, and $\sigma$, a bijection of $\{1, \dots, n\}$ that preserves compatibility and weights, carries it to an optimal schedule of the original intervals.
3. Merge sort makes at most $n\lceil \log_2 n \rceil$ comparisons. Each comparison of a binary search over a range of $m \ge 2$ indices leaves at most $\lceil m/2 \rceil$ of them, so the search for $p(j)$, over the $j$ indices $0, \dots, j - 1$, makes at most $\lceil \log_2 j \rceil \le \lceil \log_2 n \rceil$ comparisons. The table and the traceback each make at most $n$ comparisons of weights.

## Background

- [Correctness and optimality of earliest-finish interval scheduling](../../greedy-algorithms-and-matroids/interval-scheduling/interval-schedule-correct.md): the unweighted greedy algorithm, with the same compatibility relation.
- [Weighted interval scheduling exchange identity](../dynamic-programming-principles/weighted-interval-scheduling-exchange-identity.md): the same case split for an arbitrary finite family of intervals with natural weights.

## Sources

- J. Kleinberg and É. Tardos, *Algorithm Design*, Pearson/Addison-Wesley, 2005.
- K. Wayne, lecture slides for Sections 6.1–6.2 of Kleinberg and Tardos, *Algorithm Design*: weighted interval scheduling, with the recurrence, the traceback and the running time by merge sort and binary search, <https://www.cs.princeton.edu/~wayne/kleinberg-tardos/pdf/06DynamicProgrammingI.pdf>
