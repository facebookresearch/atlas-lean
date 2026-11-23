# Overpartitions into odd parts and partitions into distinct parts

Write $\mathrm{po}(m)$
for the number of overpartitions of $m$ into odd parts and $\mathrm{pd}(m)$ for the number of
partitions of $m$ into distinct parts. For every natural number $n$,
$\sum_{k \ge 0,\ k(k+1)/2 \le n} (-1)^{\lceil k/2 \rceil} \, \mathrm{po}(n - k(k+1)/2) =
\sum_{k \in \mathbb{Z},\ k(3k+1) \le n} (-1)^k \, \mathrm{pd}(n - k(3k+1))$.

The sum on the left runs over $k \ge 0$ only. Taken over all integers $k$ it would double, since
$k$ and $-1 - k$ give the same term, and the identity would fail at $n = 0$.

## Sources

- Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd Parts*, INTEGERS 26 (2026), Article A60, Theorem 14.
