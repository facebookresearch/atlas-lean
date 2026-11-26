# Cache-oblivious distribution sort

In the [ideal-cache model](the-ideal-cache-model.md) with a cache of $Z$ words and lines of $L$ words satisfying the tall-cache assumption $Z = \Omega(L^2)$, the cache-oblivious distribution sort sorts $n$ elements with $O(n \lg n)$ work and $O\bigl(1 + (n/L)(1 + \log_Z n)\bigr)$ cache misses. It partitions the input into $\sqrt n$ contiguous subarrays of size $\sqrt n$ and sorts each recursively, distributes the sorted subarrays into buckets $B_1, \dots, B_q$ of size at most $2\sqrt n$ each whose elements are ordered between the buckets, using a recursive distribution procedure and median finding to split overfull buckets, and finally sorts each bucket recursively.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 5, the algorithm, Lemmas 9 and 10 and Theorem 11.
