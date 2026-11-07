# Different parts in a residue class and partitions of nonnegative crank

Let $m$, $r$ and
$n$ be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $C(k)$ be the number of partitions of $k$ whose crank is
nonnegative. Then

$$\sum_{j \ge 0,\ j(j+1)/2 \le n} (-1)^j a_{r,m}(n - j(j+1)/2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, C(n - mj - r).$$

The companion identity of the source with the number $D(k)$ of partitions of $k$ with positive
crank is not stated: it fails for this crank, since $D(1) = 0$ while $p(1) - C(1) = 1$, where
$p(k)$ is the number of partitions of $k$ (for $m = 2$, $r = 1$, $n = 2$ its left side is $1$ and
its right side is $0$).

## Sources

- Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024), Article A15, Theorem 11 (i) (`integers-2024-A15-thm-11`).
