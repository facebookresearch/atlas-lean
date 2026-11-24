# Range queries after a point update of a built segment tree

Let $L = (x_0, \dots, x_{n-1})$
be a list with entries in an additive monoid, let $i < n$, let $y$ be an element of the monoid,
and let $L'$ be the list obtained from $L$ by replacing $x_i$ with $y$, with entries
$x'_0, \dots, x'_{n-1}$. Apply the point update at index $i$ with value $y$ to the segment tree
built from $L$. For all natural numbers $l, r$, the range query over $[l, r)$ on the result
returns $\sum_{l \le k < \min(r, n)} x'_k$, the sum taken in increasing order of $k$; it is $0$
when $\min(r, n) \le l$.
