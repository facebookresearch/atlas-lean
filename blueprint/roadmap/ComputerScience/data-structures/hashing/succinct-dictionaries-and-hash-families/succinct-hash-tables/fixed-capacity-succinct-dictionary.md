# Fixed-capacity succinct dictionary with deletions in expected amortized constant time

For every capacity $n \le U$, value bound $V$ and admissible word size, there is a randomized Word-RAM implementation of the dynamic dictionary with capacity $n$ using $\mathrm{OPT}(U, V, n) + O(n \log \log n)$ bits of memory, in which every operation takes expected amortized $O(1)$ instructions against operation sequences fixed independently of the hash seed. Keys are quotiented by a one-round Feistel permutation, grouped into buckets and micro-buckets of $\lfloor \log_2 n \rfloor$ total address bits, and stored in fixed-width full slabs with one shared tail pool, so that no slot is wasted.

## Proof sketch

The bucket and micro-bucket address bits sum to $\lfloor \log_2 n \rfloor$, so the quotients have the length allowed by the information-theoretic bound up to $O(\log \log n)$ bits per key. Expected chain lengths are $O(1)$ by pairwise independence of the Feistel bucket hash, and slab promotions and demotions are paid for by a hysteresis potential, giving amortized $O(1)$ slot allocation.

## Depends on

- [One-round Feistel quotienting of keys](one-round-feistel-quotienting.md)
- [Bounded-capacity dictionary specification](../dictionary-specifications/bounded-capacity-dictionary.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Quotient storage is succinct](quotient-storage-is-succinct.md)
- [Potential method: amortized costs bound actual costs](../../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
