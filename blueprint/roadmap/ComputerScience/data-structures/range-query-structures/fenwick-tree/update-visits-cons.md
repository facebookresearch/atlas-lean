# A valid Fenwick update step

For natural array length $n$ and one-indexed start
$1\le i\le n$, the visit list starts with $i$, followed by the update visits starting at
$i+\operatorname{lowbit}(i)$ in the same array.
