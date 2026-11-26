# Good hash seeds on a trailing window of operations

For the with-high-probability succinct dictionary with exponent $c \ge 1$ and capacity $n$ at least a threshold $2^{\Theta(c^6)}$, let the static seed consist of two independent universe-reduced salted double tabulation functions (one for buckets, one for fingerprints). For every operation sequence fixed in advance and every operation $o$ of it, the probability that the seed is *not good on the trailing window* of $O(q)$ operations before $o$ (some bucket unbalanced, reduced keys not injective, or no collision-free salt below the salt bound for some dirty bucket, or too many salt collisions in an epoch) is at most $\max(n, 1)^{-c}$.

## Proof sketch

Each bad event concerns a window of polynomially many keys; double tabulation is highly independent with high probability, and under sufficiently high independence a Chernoff-type moment bound makes each bucket's imbalance and each salt failure polynomially unlikely, with the exponent tuned by the threshold. A union bound over buckets, salts and window positions gives the claim.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)
- [Universe-reduced two-stage hashing](../word-ram-hash-families/universe-reduced-two-stage-hashing.md)

## Proof depends on

- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)
- [Multiply-shift is 2/2^M-universal](../word-ram-hash-families/multiply-shift-is-universal.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
