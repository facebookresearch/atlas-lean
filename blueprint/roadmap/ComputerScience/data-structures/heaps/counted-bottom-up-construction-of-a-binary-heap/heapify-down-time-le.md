# Heapify Down time le

For a vector of size $n$ and an index $i < n$, the counted sift-down at $i$ makes comparisons plus swaps at most $3(\lfloor \log_2 n \rfloor - \lfloor \log_2 (i + 1) \rfloor)$. The bound uses the deepest level of the whole vector, not the height of the subtree at $i$: for $n = 4$ and $i = 2$ the difference is $1$, although that node is a leaf.
