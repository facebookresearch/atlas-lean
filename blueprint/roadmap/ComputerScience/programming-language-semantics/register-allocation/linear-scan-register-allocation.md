# Linear-scan register allocation

Number the instructions of a program and, from [live-variables analysis](../static-analysis/live-variables-analysis.md), give each variable $v$ a *live interval* $[i, j]$: no instruction numbered above $j$ or below $i$ has $v$ live. Two live intervals *overlap* if they share an instruction number. With $R$ registers, the *linear-scan* algorithm processes the intervals in increasing order of start point, keeping a list of *active* intervals that currently hold registers, sorted by end point:
- at each new interval it frees the registers of active intervals that ended before its start;
- it gives the new interval a free register if there is one;
- otherwise, if the active interval that ends last ends strictly later than the new interval, it spills that active interval, gives its register to the new interval and replaces it by the new interval in the active list; if not, it spills the new interval and leaves the active list unchanged.

**Theorem.**
1. If $n > R$ live intervals overlap at some point, then in any assignment in which no two overlapping intervals share a register, at least $n - R$ of them reside in memory.
2. If at most $R$ live intervals overlap at every point, linear scan assigns a register to every interval, and no two overlapping intervals get the same register.
3. With $R \ge 1$ registers, linear scan takes time $O(V \log (R + 1))$ for $V$ intervals sorted by start point, when the active list is kept as a balanced search tree.

**Proof of part 2.** When an interval starting at $i$ is processed, the active intervals that have not been freed all contain $i$, as does the new interval; so at most $R - 1$ of them are active and a register is free.

## Depends on

- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Sources

- M. Poletto and V. Sarkar, "Linear scan register allocation", *ACM Transactions on Programming Languages and Systems* 21(5):895–913, 1999: Section 3 (live intervals), Section 4 (the algorithm, the observation that if $n > R$ intervals overlap at any point at least $n - R$ of them reside in memory, the spilling heuristic of Section 4.1, and the complexity analysis).
- A. C. Myers, *Register Allocation*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/regalloc/index.html>: section "Linear-Scan Register Allocation". The proof of part 2 is written out here.
