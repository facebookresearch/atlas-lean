# Linear probing with 5-wise independence takes expected constant probes

Consider linear probing in a table of $2^M$ slots with $2^M \ge 8 n$ (load factor at most $1/8$), storing a set of at most $n$ keys inserted in any order fixed independently of the hash function, where $h$ is drawn from a 5-wise independent family into $[2^M]$. Then for every key $x$ (present or absent) the expected number of slots inspected by a search for $x$, and by an insertion of $x$, is at most an absolute constant, independent of $n$ and $M$. On the Word RAM, with $h$ a 5-wise independent polynomial hash, this gives a dictionary with expected $O(1)$ time per operation in $O(n)$ words.

## Proof sketch

A probe sequence of length $\ell$ from $h(x)$ implies an occupied cyclic interval around $h(x)$ of length at least $\ell$, which contains an aligned dyadic interval of scale $j \approx \log_2 \ell$ holding at least $2^{j-1}$ keys, i.e. an overloaded interval at scale $j$. By the fourth-moment bound, scale $j$ is overloaded with probability at most $c / 4^j$ for an absolute constant $c$; summing $2^j$ times this over the scales gives the constant.

## Depends on

- [Open-addressing hash table](../../open-addressing/open-addressing.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Fourth-moment bucket bound under 5-wise independence](fourth-moment-bucket-bound.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](../word-ram-hash-families/polynomial-hashing-is-k-wise-independent.md)

## Sources

- A. Pagh, R. Pagh and M. Ruzic, "Linear Probing with Constant Independence", SIAM Journal on Computing 39(3), 2009.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
