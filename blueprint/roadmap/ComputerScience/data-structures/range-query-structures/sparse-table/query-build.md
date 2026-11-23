# Correctness of sparse table queries

Let $a = (a_0, \dots, a_{n-1})$ be a list over a
linearly ordered type and let $l, r$ be natural numbers with $r \le n$. Then the range-minimum
query over $[l, r)$ on the sparse table built from $a$ returns the minimum of the slice
$(a_l, \dots, a_{r-1})$ (none when $r \le l$, where the slice is empty).

No ordering premise $l \le r$ is needed.
