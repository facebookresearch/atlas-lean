# Linear probing with 5-wise independence takes expected constant probes

Consider linear probing in a table of $2^M$ slots with $2^M \ge 8 n$ (load factor at most $1/8$), storing a set of at most $n$ keys inserted in any order fixed independently of the hash function, where $h$ is drawn from a 5-wise independent family into $[2^M]$. Then for every key $x$ (present or absent) the expected number of slots inspected by a search for $x$, and by an insertion of $x$, is at most an absolute constant, independent of $n$ and $M$. On the Word RAM, with $h$ a 5-wise independent polynomial hash and $2^M$ the least power of two with $2^M \ge 8n$, this gives a dictionary with expected $O(1)$ time per operation in $O(n)$ words.

## Proof sketch

Let $S$ be the stored set and $\bar\alpha = n / 2^M \le 1/8$. The occupied set depends only on $S$ and $h$, and an operation on $x$ makes at most $1 + \max\{l : h(x) + [l] \text{ occupied}\}$ probes, so the expectation is at most $1 + \sum_{l > 0} \Pr[h(x) + [l] \text{ occupied}]$. If $h(x) + [l]$ is occupied, then either at least $\frac{1+\bar\alpha}{2} l - 1$ keys of $S \setminus \{x\}$ hash into $h(x) + [l]$, or for some $\ell$ at least $\ell + \frac{1-\bar\alpha}{2} l$ keys hash into $[h(x) - \ell, h(x))$ (Pagh, Pagh and Ružić, Lemma 4.1). The fourth-moment bound bounds the first event by $O(l^{-2})$, and a union bound over geometrically growing intervals ending at $h(x)$, again by the fourth-moment bound (their Lemma 4.2), bounds the second by $O(l^{-2})$; at load $\bar\alpha \le 1/8$ the constants are absolute, and the sum over $l$ converges (their Theorem 4.3 gives $O((1-\bar\alpha)^{-5/2})$ at every load $\bar\alpha < 1$).

## Depends on

- [Open-addressing hash table](../../open-addressing/open-addressing.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](../word-ram-hash-families/polynomial-hashing-is-k-wise-independent.md)

## Proof depends on

- [Fourth-moment bucket bound under 5-wise independence](fourth-moment-bucket-bound.md)

## Sources

- A. Pagh, R. Pagh and M. Ruzic, "Linear Probing with Constant Independence", SIAM Journal on Computing 39(3), 2009 (Lemma 4.1, Lemma 4.2, Theorem 4.3).
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
