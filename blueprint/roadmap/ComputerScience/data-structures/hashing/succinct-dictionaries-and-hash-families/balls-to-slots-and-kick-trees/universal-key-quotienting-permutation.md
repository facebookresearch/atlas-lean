# Universal key-quotienting permutation

For $m \le a$, a *key-quotienting permutation* is a random bijection $\pi : [2^a] \to [2^m] \times [2^{a-m}]$ splitting a key into a bucket index and a quotient; storing only the quotient in the bucket saves $m$ bits per key, so $n$ keys take $n(a - m)$ quotient bits in total. It is required to behave like a uniformly random permutation on small sets: for the sets of at most $\kappa$ keys on which the analysis relies (for instance, keys lying in one shard), the joint distribution of their images is within a small statistical distance $\delta$ of that under a uniformly random permutation. For polynomial-size universes the source assumes such permutations without loss of generality (Section 2.4), obtaining them from the $\kappa$-wise $\delta$-dependent permutations of Naor and Reingold (Corollary 8.1), built from pairwise independent permutations and Feistel rounds with $\kappa$-wise independent round functions, with $\delta$ driven down to $1/\mathrm{poly}(n)$ by composition, and with a one-round Feistel permutation that shards the keys so that the permutations are applied inside shards, as in Arbitman, Naor and Segev. A two-round unbalanced Feistel network whose first round is a double tabulation hash is a further instantiation; it does not appear in these sources.

## Depends on

- [One-round Feistel quotienting of keys](../succinct-hash-tables/one-round-feistel-quotienting.md)
- [Double tabulation hashing](../word-ram-hash-families/double-tabulation-hashing.md)
- [Luby–Rackoff theorem](../../../../cryptography/symmetric-key/pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Sections 2.4 and 5.3).
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010 (Sections 5.2 and 5.3).
- M. Naor and O. Reingold, "On the Construction of Pseudorandom Permutations: Luby-Rackoff Revisited", Journal of Cryptology 12(1), 1999.
- E. Kaplan, M. Naor and O. Reingold, "Derandomized Constructions of k-Wise (Almost) Independent Permutations", Algorithmica 55(1), 2009.
