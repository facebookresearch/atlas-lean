# Lower-bound search

Given an array $a = (a_0, \dots, a_{n-1})$ over a linearly ordered type and
a key $k$, lower-bound search maintains a half-open interval $[l, h)$ of indices, starting from
$[0, n)$. While $l < h$, it compares $a_m$ with $k$ at the midpoint
$m = l + \lfloor (h - l)/2 \rfloor$, charging one unit for this comparison, and continues with
$[m + 1, h)$ if $a_m < k$ and with $[l, m)$ otherwise. When $l = h$ it returns $l$.

When $a$ is sorted in nondecreasing order (or at least partitioned at $k$: every entry before the
returned index is $< k$ and every entry from that index on is $\ge k$), the result is the first
index $i$ with $k \le a_i$, or $n$ if every entry is below $k$. On an unsorted array the result is
unspecified: for $a = (2, 1)$ and $k = 2$ the search returns $2$, not the first index $0$ with
$k \le a_0$.
