# Sampled locate takes at most $s - 1$ LF steps

Let $t = t_0 \cdots t_{n-1}$ be a text over a linearly ordered alphabet, let $SA$ be the suffix
array of $t$ followed by a sentinel smaller than every letter, and let $s \ge 1$. Suppose a sampling
stores a value for every row $r \le n$ with $SA[r] \equiv 0 \pmod{s}$. Then for every $k$ and every
row $r \le n$, the number of LF steps taken by the $k$-step locate from row $r$ on the
Burrows–Wheeler transform of $t$ is at most $SA[r] \bmod s$, hence at most $s - 1$.
