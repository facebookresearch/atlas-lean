# Myers' bit-vector algorithm for approximate string matching

For a pattern $P$ of length $m$ and a text $T$ of length $n$, let $C$ be the unit-cost dynamic-programming table for approximate matching with boundary condition $C[0, j] = 0$, so that the matches with at most $k$ differences end at the positions $j$ with $C[m, j] \le k$. All horizontal and vertical differences between adjacent entries of $C$ lie in $\{-1, 0, 1\}$ (Myers 1999, Lemma 1, attributed there to Masek–Paterson and Ukkonen), so a column is determined by its vertical deltas. Myers encodes these deltas by two bit-vectors and computes each new column with a constant number of word operations when $m$ is at most the word length $w$. This gives an $O(n\lceil m/w\rceil)$ algorithm, independent of $k$, for finding all text positions where $P$ matches with at most $k$ differences, and, by computing blocks inside Ukkonen's zone, an $O(kn/w)$ expected-time algorithm for long patterns.

## Expansion

1. The approximate matching table, its recurrence and boundary condition; compare the [edit distance cell transitions](../../../ComputerScience/string-algorithms/edit-distance/edit-distance-cell-transitions.md).
2. Lemma 1: adjacent differences lie in $\{-1, 0, 1\}$.
3. The bit-vector encoding of a column and the word-parallel scanning step, including the addition that resolves horizontal dependencies.
4. The $O(n\lceil m/w\rceil)$ bound for long patterns by blocking, and the $O(kn/w)$ expected bound.

## Sources

- G. Myers, A fast bit-vector algorithm for approximate string matching based on dynamic programming, J. ACM 46 (1999), 395–415, Lemma 1. <https://doi.org/10.1145/316542.316550>
