# Fenwick prefix visits

For a natural array length $n$ and requested prefix length $k$,
the list of one-indexed stored entries read by the walk starts at $\min(k,n)$ and repeatedly
subtracts the current index's lowest set bit, stopping before index $0$. The returned list is
in visit order. It is empty if $k=0$ or $n=0$, and a request past the end reads the full prefix.
