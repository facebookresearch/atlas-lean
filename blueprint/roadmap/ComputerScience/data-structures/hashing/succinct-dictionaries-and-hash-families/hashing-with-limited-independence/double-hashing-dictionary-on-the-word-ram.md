# Open addressing with odd-stride double hashing on the Word RAM

For keys in a universe of size polynomial in $n$, there is a Word-RAM implementation of the insert-only bounded dictionary with capacity $n$ by open addressing with odd-stride double hashing in a power-of-two table of at least $2n$ slots, with the hash pair drawn from $(2L+1)$-wise independent polynomial hashing below a size threshold and from double tabulation above it ($L = \lceil \log_2 \max(n,4)\rceil + 4$). It uses $O(n)$ words, and against every operation sequence fixed in advance each query and insertion takes $O(1)$ expected instructions.

## Proof sketch

The work of an operation is linear in its number of probes, which has expectation $O(1)$ by the double hashing bound under limited independence; evaluating the hash pair takes $O(L)$ or $O(1)$ instructions depending on the regime, and the threshold is chosen so that this cost is constant for small tables.

## Depends on

- [Odd-stride double hashing in power-of-two tables](odd-stride-double-hashing.md)
- [Bounded-capacity dictionary specification](../dictionary-specifications/bounded-capacity-dictionary.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Double hashing with limited independence takes expected constant probes](double-hashing-with-limited-independence.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](../word-ram-hash-families/polynomial-hashing-is-k-wise-independent.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- J. P. Schmidt and A. Siegel, "The Analysis of Closed Hashing under Limited Randomness", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
