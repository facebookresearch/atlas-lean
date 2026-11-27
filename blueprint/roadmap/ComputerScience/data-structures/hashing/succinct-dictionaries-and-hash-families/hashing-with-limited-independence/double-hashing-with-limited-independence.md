# Double hashing with limited independence takes expected constant probes

Let $2 n \le 2^M$ and let $L = \lceil \log_2 \max(n, 4) \rceil + 4$. Consider an open-addressed table of $2^M$ slots filled by inserting at most $n$ keys with odd-stride double hashing, in an order fixed before the hash functions are drawn. If $(h_1, h_2)$ is $(2L + 1)$-wise independent, then the expected number of probes of an unsuccessful search (equivalently, of inserting a fresh key) is at most an absolute constant $C$, independent of $n$ and $M$. The same holds, with a larger absolute constant, if instead $(h_1, h_2)$ is drawn by double tabulation with high-probability $(2L+1)$-wise independence on a universe of size polynomial in $n$.

## Proof sketch

Probes beyond the first $L$ are rare: by the $(2L+1)$-wise independence of the stored keys' probe positions and the query's first $L$ probe positions, the probability that the first $i \le L$ probes all hit occupied slots is at most $c_0\,2^{-i}$ for an absolute constant $c_0$, as under uniform hashing at load $1/2$, so the first $L$ probes contribute $O(1)$ in expectation. The tail beyond $L$ is bounded by $n + 1$ probes times the probability $c_0\,2^{-L} \le c_0/(16n)$ that the first $L$ probes are all occupied, which is again $O(1)$. Under double tabulation the failure probability of independence adds a lower-order term.

## Depends on

- [Odd-stride double hashing in power-of-two tables](odd-stride-double-hashing.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Expected probes in open addressing](../../hashing-analysis/expected-probes-in-open-addressing.md)

## Proof depends on

- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)

## Sources

- J. P. Schmidt and A. Siegel, "The Analysis of Closed Hashing under Limited Randomness", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
