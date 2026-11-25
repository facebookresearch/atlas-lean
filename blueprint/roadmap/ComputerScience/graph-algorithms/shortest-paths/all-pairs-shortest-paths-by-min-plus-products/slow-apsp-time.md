# Exact operation counts of SLOW-APSP

For all $n \times n$ matrices $W$ and $L^{(0)}$ over
the min-plus semiring on $\mathbb{Z} \cup \{\infty\}$, the cost of SLOW-APSP on $W$ and $L^{(0)}$
is the triple $(n^2 + 2(n-1)n^2,\ (n-1)n^3,\ (n-1)n^3)$ of cell assignments (copies and fills),
scalar additions and scalar minimums, where $n - 1$ means $\max(n - 1, 0)$.

The assignment count excludes the accumulator updates inside the min-plus accumulation loop.
