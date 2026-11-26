# False-positive rate of the two-stage quotient filter

Let the quotient be produced by a two-stage 5-wise independent hash into $b$ bits with $2^b \ge 8 n$, and the remainder by an independent multiply-shift hash into $f = k + 1$ bits (or fewer if keys are shorter). Then for every set $S$ with $|S| \le n$ and every key $u \notin S$, the probability that the filter reports $u$ as present is at most $2^{-k}$. Furthermore the quotient hash is $2/2^b$-universal, and the expected cluster length is $O(1)$, so on the Word RAM with bit-packed slot arrays every insertion, deletion and query takes expected $O(1)$ instructions against sequences fixed in advance, using $2^b (f + 3)$ bits plus $O(1)$ words.

## Proof sketch

A false positive requires some $v \in S$ with $q(v) = q(u)$ and $r(v) = r(u)$; the two hashes are independent, so by universality each $v$ contributes at most $\frac{2}{2^b} \cdot \frac{2}{2^f}$, and the union bound over $|S| \le n \le 2^b / 8$ keys gives at most $2^{-f+1} \cdot \frac{1}{2} \le 2^{-k}$ when $f = k+1$. Cluster lengths are bounded as for linear probing with 5-wise independence at load at most $1/8$.

## Depends on

- [Quotient filter](quotient-filter.md)
- [Dynamic approximate-membership filter](dynamic-approximate-membership-filter.md)

## Proof depends on

- [Multiply-shift is 2/2^M-universal](../word-ram-hash-families/multiply-shift-is-universal.md)
- [Canonical layout and correctness of quotient-filter updates](canonical-quotient-filter-layout.md)
- [Linear probing with 5-wise independence takes expected constant probes](../hashing-with-limited-independence/linear-probing-with-five-wise-independence.md)

## Sources

- A. Pagh, R. Pagh and S. S. Rao, "An Optimal Bloom Filter Replacement", Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2005.
- M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes, P. Shetty, R. P. Spillane and E. Zadok, "Don't Thrash: How to Cache Your Hash on Flash", Proceedings of the VLDB Endowment 5(11), 2012.
- A. Pagh, R. Pagh and M. Ruzic, "Linear Probing with Constant Independence", SIAM Journal on Computing 39(3), 2009.
