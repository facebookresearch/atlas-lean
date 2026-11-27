# Succinct dynamic dictionary with constant time with high probability

For every constant $c > 0$ there are constants $C_1, C_2$ such that for all $n \le U$, $V$ and word sizes $w > 0$ with $U$, $V$ and the address range fitting in a word, there is a Word-RAM implementation of the dynamic dictionary (insert, delete, query) with capacity $n$ that

1. occupies at most $\lceil (\mathrm{opt}(U, V, n) + C_1 n \lceil \log_2 \lceil \log_2 \max(n, 4) \rceil \rceil) / w \rceil + C_2$ words, i.e. $\mathrm{OPT} + O_c(n \log \log n)$ bits;
2. executes every operation within a fixed $O_c(1)$ worst-case instruction budget, except with probability at most $n^{-c}$ per operation, against every operation sequence fixed in advance;
3. is always correct: on the rare failure events it falls back to a slower representation (a compressed sparse row layout) and later heals back to the fast mode.

## Proof sketch

The fast mode is a partition hash table whose buckets are rebuilt in the background, a constant amount of work per operation (deamortized global rebuilding over epochs). A static seed made of two universe-reduced double tabulation functions is good on the trailing window of operations with probability at least $1 - n^{-c}$; on a good seed every bucket stays balanced, fingerprints are injective after a bounded number of salt retries, and no guard of the fast path fires. Correctness on every seed follows from the exact refinement of the dictionary by each mode and the transitions between them.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](partition-hash-table.md)
- [Bounded-capacity dictionary specification](../dictionary-specifications/bounded-capacity-dictionary.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Quotient storage is succinct](quotient-storage-is-succinct.md)
- [Word-parallel rank of packed fingerprints](word-parallel-rank-of-packed-fingerprints.md)
- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)
- [Universe-reduced two-stage hashing](../word-ram-hash-families/universe-reduced-two-stage-hashing.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
- M. H. Overmars, "The Design of Dynamic Data Structures", Lecture Notes in Computer Science 156, Springer, 1983.
