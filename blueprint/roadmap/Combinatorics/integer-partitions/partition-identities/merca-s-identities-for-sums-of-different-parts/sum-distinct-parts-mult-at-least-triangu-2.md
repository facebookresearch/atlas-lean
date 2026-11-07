# Signed triangular sum of $s_m$ and nonnegative crank

Let $m \ge 1$ and $n$ be natural
numbers. Write $s_m(k)$ for the sum of the different parts that appear at least $m$ times in
partitions of $k$, and $C(k)$ for the number of partitions of $k$ with nonnegative crank. Then

$$
\sum_{j \ge 0,\ j(j+1)/2 \le n} (-1)^j s_m\bigl(n - j(j+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, C(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges. Part (ii) (with $D(k)$, positive
crank) is omitted: it is false for this crank ($m = 1$, $n = 2$: left side $s_1(1) = 1$, right
side $D(1) + 2 D(0) = 0$).

## Sources

- Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024), Article A15, Theorem 12 (i) (`integers-2024-A15-thm-12`).
