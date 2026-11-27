# Dynamic approximate-membership filter

A *dynamic approximate-membership filter* with universe $[U]$, capacity $n$ and false-positive bound $\varepsilon$ represents a set $S \subseteq [U]$, initially empty, under $\mathrm{insert}(u)$ (admissible when $u \notin S$ and $|S| < n$), $\mathrm{delete}(u)$ (admissible when $u \in S$) and $\mathrm{query}(u)$. On every operation sequence fixed in advance, every query of a key $u \in S$ answers yes (no false negatives), and every query of a key $u \notin S$ answers yes with probability at most $\varepsilon$ (false positive), where the probability is over the filter's randomness.

## Depends on

- [Oblivious-sequence specification of a randomized data structure](../../../data-structure-interfaces-and-refinement/oblivious-sequence-specification.md)
- [Bloom filter](../../bloom-filter/bloom-filter.md)

## Sources

- A. Pagh, R. Pagh and S. S. Rao, "An Optimal Bloom Filter Replacement", Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2005.
- M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes, P. Shetty, R. P. Spillane and E. Zadok, "Don't Thrash: How to Cache Your Hash on Flash", Proceedings of the VLDB Endowment 5(11), 2012.
