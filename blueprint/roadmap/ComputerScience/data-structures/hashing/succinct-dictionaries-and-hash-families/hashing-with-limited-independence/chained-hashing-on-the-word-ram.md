# Chained hashing with multiply-shift on the Word RAM

For keys in $[U]$ and capacity $n$, let $2^M$ be the least power of two with $2^M \ge \max(n, 2)$ and let $w_0 = \max(M, \lceil \log_2 \max(U, 2) \rceil)$, with word size $w \ge 2 w_0$. For values below $V$, where $V < 2^w$ so that every stored value fits in one $w$-bit word, a chained hash table with $2^M$ bucket heads, a pool of $n$ nodes and a multiply-shift hash function uses $O(n)$ words and implements the insert-only bounded dictionary. Against any operation sequence fixed independently of the seed, each query and insertion runs in expected $O(1)$ Word-RAM instructions, and initialization takes $O(1)$ instructions on zeroed memory.

## Proof sketch

The work of an operation on key $x$ is linear in the length of the chain of $h(x)$. By the $2/2^M$-universality of multiply-shift, each other stored key lies in that chain with probability at most $2/2^M$, so the expected chain length is at most $1 + 2n / 2^M \le 3$.

## Depends on

- [Hash table with separate chaining](../../hash-table-with-separate-chaining/hash-table.md)
- [Multiply-shift hashing](../word-ram-hash-families/multiply-shift-hashing.md)
- [Bounded-capacity dictionary specification](../dictionary-specifications/bounded-capacity-dictionary.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Multiply-shift is 2/2^M-universal](../word-ram-hash-families/multiply-shift-is-universal.md)
- [Expected chain length under universal hashing](../../hashing-analysis/expected-chain-length-under-universal-hashing.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, "A Reliable Randomized Algorithm for the Closest-Pair Problem", Journal of Algorithms 25(1), 1997.
