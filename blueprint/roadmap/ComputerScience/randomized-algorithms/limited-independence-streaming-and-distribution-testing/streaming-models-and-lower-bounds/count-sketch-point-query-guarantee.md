# Count-Sketch point-query guarantee

The *Count-Sketch* maintains $d = 2r$ rows of $w$ counters with a pairwise independent bucket hash $h_j : U \to [w]$ and a pairwise independent sign hash $g_j : U \to \{\pm 1\}$ per row; reading item $a$ adds $g_j(a)$ to counter $h_j(a)$ in each row, and a point query for $a$ returns the median over rows of $g_j(a) \cdot C_j[h_j(a)]$. For every stream with frequency vector $f$ and every item $a$, the estimate $\hat f_a$ satisfies $|\hat f_a - f_a| \le \sqrt{3/w}\,\|f_{-a}\|_2$ with probability at least $1 - e^{-\Omega(r)}$, using $O(r w \log m)$ bits.

## Proof sketch

In one row, $g_j(a) C_j[h_j(a)] - f_a = \sum_{b \ne a, h_j(b) = h_j(a)} g_j(a)g_j(b) f_b$ has mean $0$ and variance at most $\|f_{-a}\|_2^2/w$; Chebyshev gives error at most $\sqrt{3/w}\|f_{-a}\|_2$ with probability at least $2/3$, and the median of $2r$ independent rows fails only if half of them fail (Chernoff).

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)
- [Frequency moment of a stream](../../frequency-moments-of-data-streams/freq-moment.md)

## Sources

- M. Charikar, K. Chen and M. Farach-Colton, "Finding Frequent Items in Data Streams", Theoretical Computer Science 312(1), 2004.
- A. Chakrabarti, "Data Stream Algorithms: Lecture Notes", Dartmouth College, 2020.
