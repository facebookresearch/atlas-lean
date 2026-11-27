# Cuckoo hashing on the Word RAM in expected amortized constant time

For keys in a universe of size at most $\max(n,4)^{c}$ for a constant $c$, there is a Word-RAM implementation of the insert-only bounded dictionary with capacity $n$ by two-table cuckoo hashing, using $O_c(n + 1)$ words: two sub-tables of size at least $32 \max(n,4)$, a hash pair that is $(2L+2)$-wise independent polynomial hashing, for an eviction cap $L = O(\log n)$, for small $n$ and double tabulation for large $n$, and arrays recording the insertion order. Lookups make two probes in the worst case. Against every operation sequence fixed independently of the seeds, the expected total number of instructions is $O(1)$ per operation, amortized over the sequence. Pagh and Rodler prove worst-case two-probe lookups and expected amortized constant-time insertions with Siegel's hash functions; the instantiation by polynomial hashing and double tabulation with the sizes above is not stated in the cited sources.

## Proof sketch

Lookups read the two candidate slots. Insertions perform a displacement walk whose expected length is bounded by the walk constant, and exceed the cap with probability $O(1/n^2)$, in which case Las Vegas rehashing costs $O(n)$ expected work. Summing over the sequence gives expected amortized $O(1)$.

## Depends on

- [Bounded-capacity dictionary specification](../dictionary-specifications/bounded-capacity-dictionary.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)
- [Cuckoo hash table](../../cuckoo-hashing/cuckoo-hashing.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](../word-ram-hash-families/polynomial-hashing-is-k-wise-independent.md)
- [Double tabulation hashing](../word-ram-hash-families/double-tabulation-hashing.md)

## Proof depends on

- [Cuckoo hashing with O(log n)-wise independent hash pairs](cuckoo-hashing-with-logarithmic-independence.md)
- [Las Vegas rehashing for cuckoo hashing](las-vegas-rehashing-for-cuckoo-hashing.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
