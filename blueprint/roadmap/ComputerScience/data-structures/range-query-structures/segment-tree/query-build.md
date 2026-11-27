# Range queries on a built segment tree

Let $L = (x_0, \dots, x_{n-1})$ be a list with
entries in an additive monoid and let $l, r$ be natural numbers. The range query over $[l, r)$ on
the segment tree built from $L$ returns $\sum_{l \le k < \min(r, n)} x_k$, the sum taken in
increasing order of $k$; it is $0$ when $\min(r, n) \le l$.
