# Garden of Eden identity for $s_m$

Let $m \ge 1$ and $n$ be natural numbers. Write
$s_m(k)$ for the sum of the different parts that appear at least $m$ times in partitions of
$k$, and $G(k)$ for the number of Garden of Eden partitions of $k$, those whose Dyson rank is
at most $-2$ (so $G(0) = 0$). Then

$$
\sum_{j \ge 1,\ 3j(j+1)/2 \le n} (-1)^{j+1} s_m\bigl(n - 3j(j+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, G(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges.

## Sources

- Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024), Article A15, Theorem 10 (ii) (`integers-2024-A15-thm-10`).
