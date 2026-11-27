# Universal key-quotienting permutation

For $m \le a$, a *key-quotienting permutation* is a bijection $[2^a] \to [2^m] \times [2^{a-m}]$ splitting a key into a bucket index and a quotient, built so that for sets of at most $\kappa$ keys lying in one shard the bucket indices are, with probability $1 - \delta$, distributed like those of a uniformly random permutation up to small statistical distance. It is constructed from a two-round unbalanced Feistel network with double tabulation round functions on a polynomial universe, and from unbalanced three-round Naor–Reingold Feistel blocks combined with one-round Feistel sharding for small universes. Storing only the quotient saves $m$ bits per key, so $n$ keys take $n(a - m)$ quotient bits in total.

## Depends on

- [One-round Feistel quotienting of keys](../succinct-hash-tables/one-round-feistel-quotienting.md)
- [Double tabulation hashing](../word-ram-hash-families/double-tabulation-hashing.md)
- [Luby–Rackoff theorem](../../../../cryptography/symmetric-key/pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
- M. Naor and O. Reingold, "On the Construction of Pseudorandom Permutations: Luby-Rackoff Revisited", Journal of Cryptology 12(1), 1999.
