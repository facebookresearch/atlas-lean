# Myers' bit-vector algorithm for approximate string matching

For a nonempty pattern $P$ of length $m \ge 1$ and a text $T$ of length $n$, let $C$ be the unit-cost dynamic-programming table for approximate matching with boundary condition $C[0, j] = 0$, so that the matches with at most $k$ differences end at the positions $j$ with $C[m, j] \le k$. All horizontal and vertical differences between adjacent entries of $C$ lie in $\{-1, 0, 1\}$ (Myers 1999, Lemma 1, attributed there to Masek–Paterson and Ukkonen), so a column is determined by its vertical deltas. Myers encodes these deltas by two bit-vectors and computes each new column with a constant number of word operations when $m$ is at most the word length $w$. This gives a deterministic $O(n\lceil m/w\rceil)$ worst-case algorithm, independent of $k$ and valid for every $k \ge 0$ and every alphabet, for finding all text positions where $P$ matches with at most $k$ differences. Separately, Myers (Section 4) computes only the blocks of $w$ rows that meet Ukkonen's zone, the prefix of each column ending at its last entry at most $k$. The zone has no useful worst-case bound: for $P = a^m$ and $T = a^n$ with $n$ much larger than $m$, every late column is zero throughout, so the zone has depth $m$ even for $k = 1$. A bound holds only on average, for random text whose letters are independent and uniformly distributed over a fixed finite alphabet of size at least $2$ (on a one-letter alphabet the random text is $a^n$ and the example above applies): by the bound of Chang and Lampe that Myers uses, the expected zone size is then $O((k + 1)n)$ for every $k \ge 0$, with a constant depending on the alphabet size (for $k = 0$ the row-zero entries alone give $n$ cells). Counting at least one block per column, the blocked algorithm then runs in expected time $O(n + kn/w)$.

## Expansion

1. The approximate matching table, its recurrence and boundary condition; compare the [edit distance cell transitions](../../../ComputerScience/string-algorithms/edit-distance/edit-distance-cell-transitions.md).
2. Lemma 1: adjacent differences lie in $\{-1, 0, 1\}$.
3. The bit-vector encoding of a column and the word-parallel scanning step, including the addition that resolves horizontal dependencies.
4. The deterministic $O(n\lceil m/w\rceil)$ bound for long patterns by blocking.
5. Separate target: for random text over a fixed finite alphabet of at least two letters, the Chang–Lampe bound $O((k + 1)n)$, $k \ge 0$, on the expected zone size and the resulting expected time $O(n + kn/w)$ of the block-based zone algorithm.

## Sources

- G. Myers, A fast bit-vector algorithm for approximate string matching based on dynamic programming, J. ACM 46 (1999), 395–415, Lemma 1 and Section 4. <https://doi.org/10.1145/316542.316550>
- W. I. Chang and J. Lampe, Theoretical and empirical comparisons of approximate string matching algorithms, in Combinatorial Pattern Matching (CPM 1992), Lecture Notes in Computer Science 644, Springer, 1992, 175–184.
