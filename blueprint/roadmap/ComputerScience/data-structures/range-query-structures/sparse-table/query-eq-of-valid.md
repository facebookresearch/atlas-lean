# Correctness of queries on valid sparse tables

Let $t$ be a valid sparse table over a
linearly ordered type whose data is the list $(a_0, \dots, a_{n-1})$, and let $l, r$ be natural
numbers with $r \le n$. Then the range-minimum query over $[l, r)$ on $t$ returns the minimum of
the slice $(a_l, \dots, a_{r-1})$ (none when $r \le l$, where the slice is empty).

Only the premise $r \le n$ is needed: for reversed bounds $r \le l$ both sides are none.
