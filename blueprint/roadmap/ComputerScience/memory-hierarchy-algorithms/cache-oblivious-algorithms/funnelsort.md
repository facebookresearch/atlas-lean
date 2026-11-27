# Funnelsort

In the [ideal-cache model](the-ideal-cache-model.md) with a cache of $Z$ words and lines of $L$ words satisfying the tall-cache assumption $Z = \Omega(L^2)$, the cache-oblivious sorting algorithm funnelsort sorts $n$ elements with $O(n \lg n)$ work and

$$
O\bigl(1 + (n/L)(1 + \log_Z n)\bigr)
$$

cache misses. Funnelsort splits the input into $n^{1/3}$ contiguous arrays of size $n^{2/3}$, sorts them recursively, and merges the sorted sequences with an $n^{1/3}$-merger, a recursively laid-out merging device built from $\sqrt k$ left $\sqrt k$-mergers, buffers and one right $\sqrt k$-merger, which can be laid out in $O(k^2)$ contiguous memory locations.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Proof depends on

- [k-mergers](k-mergers.md)
- [A k-merger fits in quadratic space](a-k-merger-fits-in-quadratic-space.md)
- [Cache complexity of a k-merger](cache-complexity-of-a-k-merger.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4, Lemmas 4–6 and Theorem 7.
