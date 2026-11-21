# Binary search for the first occurrence

Given an array $a = (a_0, \dots, a_{n-1})$ over a
linearly ordered type and a key $k$, binary search for the first occurrence of $k$ in $a$ runs
lower-bound search for $k$ in $a$, obtaining an index $\ell$. If $\ell < n$, it makes one further
comparison, charged one unit, and returns $\ell$ when $a_\ell = k$ and no index otherwise; if
$\ell \ge n$, it returns no index without further cost.

When $a$ is sorted in nondecreasing order, the result is the first index $i$ with $a_i = k$, or no
index when $k$ does not occur in $a$. On an unsorted array a present key can be missed and the
result can be no index.
