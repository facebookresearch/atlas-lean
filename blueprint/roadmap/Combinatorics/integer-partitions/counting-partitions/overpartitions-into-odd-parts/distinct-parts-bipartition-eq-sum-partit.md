# Bipartitions into distinct parts from the partition function

Let $q(n)$ be the number of
ordered pairs of partitions into distinct parts whose sizes add up to $n$, and let $p(m)$ be the
number of partitions of $m$. For every $n \ge 0$, $q(n) = \sum_{k \ge 0} p(n - k(k+1)/2)$, where
the sum runs over the $k$ with $k(k+1)/2 \le n$.

The source states this for $n > 0$; it also holds at $n = 0$, where both sides equal $1$.

## Sources

- Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd Parts*, INTEGERS 26 (2026), Article A60, Theorem 12 (`integers-2026-A60-thm-12`).
