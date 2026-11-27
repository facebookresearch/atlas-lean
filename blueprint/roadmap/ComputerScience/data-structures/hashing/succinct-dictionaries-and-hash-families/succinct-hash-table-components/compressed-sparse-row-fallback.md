# Compressed sparse row fallback dictionary

The *compressed sparse row* (CSR) representation of a bucketed dictionary with $M$ buckets of arbitrary loads $X_0, \dots, X_{M-1}$, $\sum_b X_b \le n$, stores the prefix sums $\mathrm{start}[0..M]$ of the loads followed by the Feistel quotients and values of the items of each bucket in bucket order. It uses $\mathrm{OPT}(U, V, n) + o(n)$ bits plus the prefix sums, supports query, insertion and deletion exactly for every hash seed (more slowly than the balanced fast mode), and admits an overflow-free procedure that decides whether the current seed is good (all buckets balanced and fingerprints collision-free after salting), which is used to return to the fast mode.

## Depends on

- [One-round Feistel quotienting of keys](../succinct-hash-tables/one-round-feistel-quotienting.md)
- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
