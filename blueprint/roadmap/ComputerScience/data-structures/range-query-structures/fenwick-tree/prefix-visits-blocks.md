# Fenwick prefix blocks partition the prefix

For natural array length $n$ and query length
$k$, reverse the visit list (so the blocks are read from left to right) and concatenate the
zero-indexed array intervals $[j-\operatorname{lowbit}(j),j)$ of the visited stored endpoints
$j$. The result is exactly the consecutive list of positions from $0$ up to but excluding
$\min(k,n)$, in increasing order, without omissions or repetitions. It is empty when
$k=0$ or $n=0$, and uses the entire array when $k \ge n$.
