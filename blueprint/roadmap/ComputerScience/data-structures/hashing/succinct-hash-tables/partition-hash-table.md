# Partition hash table with fingerprint-indexed buckets

A *partition hash table* for at most $n$ keys splits the keys by a bucket hash into $B \approx n / \mathrm{polylog}(n)$ buckets, each of capacity a constant factor above its expected load $\Theta(\mathrm{polylog}(n))$. Inside a bucket, each key is stored as its Feistel quotient together with its value, and located through a *query mapper* indexed by a short fingerprint of $O(\log \log n)$ bits: a small search structure (for instance a B-tree of fanout $\Theta(\sqrt{\log n})$ navigated with word-parallel comparisons) mapping fingerprints to slot positions inside the bucket. Keys that overflow their bucket go to a shared backyard pool, and keys whose fingerprints collide inside a bucket go to a small buffer. The design uses $\mathrm{OPT}(U, V, n) + O(n \log \log n)$ bits.

## Depends on

- [One-round Feistel quotienting of keys](one-round-feistel-quotienting.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
