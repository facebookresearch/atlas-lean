# Parameter inequalities of the high-probability succinct dictionary

For every $c \ge 1$ and every capacity $n$ at least the threshold $2^{\beta(c)}$ with $\beta(c) = \Theta(c^6)$: the packed fingerprint and value words of the query mapper fit strictly below $\lfloor \log_2 n \rfloor$ bits; the character width of the double tabulation hash is large enough for Thorup's $k$-uniqueness condition at the required independence; the slab scale is at most the cube of the query-mapper fanout; the backyard pool can absorb the total overflow of the front yards whenever all buckets are balanced, for every number of stored keys up to $n$; and the total allocated space is within the succinct word budget for every word size $w$ and every $n \le U$.

## Proof sketch

Each inequality compares explicit functions of $\log_2 n$ and $\log_2 \log_2 n$ with constants depending on $c$; above the threshold, $\log_2 n$ dominates every fixed polynomial in $c$ times $\log \log n$, which gives each claim.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)
- [Succinct word budget for dictionaries](../dictionary-specifications/succinct-word-budget.md)

## Proof depends on

- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
