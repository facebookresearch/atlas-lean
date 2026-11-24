# Weighted interval scheduling

Let intervals $1, \dots, n$ with weights $w_j \ge 0$ be sorted by finish time, and let $p(j)$ be the largest index $i < j$ whose interval is compatible with (does not overlap) interval $j$, or $0$ if none. Then the maximum weight $\mathrm{OPT}(j)$ of a set of pairwise compatible intervals among the first $j$ satisfies $\mathrm{OPT}(0) = 0$ and $\mathrm{OPT}(j) = \max(w_j + \mathrm{OPT}(p(j)),\ \mathrm{OPT}(j - 1))$. Computing $p$ by binary search and the recurrence bottom-up gives an optimal set in $O(n \log n)$ time.

## Proof depends on

- [Weighted interval scheduling exchange identity](weighted-interval-scheduling-exchange-identity.md)

## Sources

- J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2005
