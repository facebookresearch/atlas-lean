# Each base pairs at most once

If $w(i, j) \ge 0$ for all $i, j$, then for every position $i$ of a sequence of length $n$,

$$\sum_{j=0}^{n-1} \bigl(P(i, j) + P(j, i)\bigr) \le 1,$$

where $P$ is the [base-pair probability](pair-prob.md).
