# Correctness of range queries on a valid segment tree

Let $t$ be a valid segment tree with
values in an additive monoid, let $(x_0, \dots, x_{n-1})$ be its leaf values from left to right,
and let $l, r$ be natural numbers. The range query over $[l, r)$ on $t$ returns
$\sum_{l \le k < \min(r, n)} x_k$, the sum taken in increasing order of $k$; it is $0$ when
$\min(r, n) \le l$.
