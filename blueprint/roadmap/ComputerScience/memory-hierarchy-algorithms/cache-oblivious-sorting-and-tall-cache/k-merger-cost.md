# Space and cache complexity of a k-merger

A $k$-merger occupies $O(k^2)$ contiguous memory. Under the tall-cache assumption $Z = \Omega(L^2)$, one invocation, producing $k^3$ output elements, incurs $O\!\left(k + \frac{k^3}{L}\left(1 + \log_Z k\right)\right)$ cache misses.

## Proof sketch

The space satisfies $S(k) = (\sqrt{k} + 1) S(\sqrt{k}) + O(k^2)$, which solves to $O(k^2)$. For the cache analysis, consider the recursion level at which the mergers $J$ have size $O(Z)$, i.e. $j^2 = O(Z)$ with $j$ the merger order; such a merger and one block of each of its inputs and outputs fit in cache when $j \le \sqrt{Z}$ and $Z = \Omega(L^2)$, so its invocations cost $O(j + j^3/L)$ misses. Each element passes through $O(\log_Z k)$ such mergers, and charging buffer refills to the elements moved gives the bound.

## Depends on

- [The k-merger (funnel)](k-merger.md)
- [Tall-cache assumptions](tall-cache-assumption.md)
- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Matteo Frigo, Charles E. Leiserson, Harald Prokop, Sridhar Ramachandran, "Cache-Oblivious Algorithms", FOCS (1999); ACM Transactions on Algorithms 8(1) (2012).
- Harald Prokop, "Cache-Oblivious Algorithms", Master's thesis, Massachusetts Institute of Technology (1999).
