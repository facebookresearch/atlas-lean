# Suffix arrays in optimal compressed space

Every string $T$ of length $n$ over an alphabet of size $\sigma$ with substring complexity $\delta$ has an index of $O\!\left(\delta\log\frac{n\log\sigma}{\delta\log n}\right)$ words that answers suffix-array queries (returning $\mathrm{SA}[i]$ for given $i$) and inverse suffix-array queries in $O(\log^{4+\varepsilon} n)$ time for any constant $\varepsilon > 0$. Hence the most powerful classical queries cost no more space than random access, collapsing the hierarchy of compressed text indexes into a single space bound, previously $O(r\log\frac{n}{r})$ with $r \ge \delta$.

## Proof sketch

Kempa and Kociumaka combine deterministic restricted recompression with $\delta$-compressed string synchronizing sets, which select $O(n/\tau)$ positions consistently across equal contexts of length $\Theta(\tau)$, with $\delta$-bounded representations at each of $O(\log n)$ scales $\tau = 2^i$: at each scale, the sorted order of synchronizing positions is determined by a structure of size $O(\delta)$ times a logarithmic factor matched to the space bound, and suffix-array queries are resolved by descending through the scales, using random access and longest-common-extension queries, each costing polylogarithmic time.

## Depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Substring complexity $\delta$](../string-attractors-and-repetitiveness-measures/substring-complexity.md)

## Proof depends on

- [Random access in $\delta$-optimal compressed space](delta-optimal-random-access.md)

## Sources

- Dominik Kempa, Tomasz Kociumaka, "Collapsing the Hierarchy of Compressed Data Structures: Suffix Arrays in Optimal Compressed Space", FOCS (2023), arXiv:2308.03635.
