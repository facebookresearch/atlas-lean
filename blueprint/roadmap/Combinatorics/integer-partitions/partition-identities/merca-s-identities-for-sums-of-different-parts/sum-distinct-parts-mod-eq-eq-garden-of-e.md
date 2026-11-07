# Different parts in a residue class and Garden of Eden partitions

Let $m$, $r$ and $n$ be
natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all partitions
of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per partition
whatever its multiplicity. Let $G(k)$ be the number of Garden of Eden partitions of $k$, that is,
partitions of $k$ whose Dyson rank (largest part minus number of parts) is at most $-2$. Then

$$\sum_{j \ge 1,\ 3j(j+1)/2 \le n} (-1)^{j+1} a_{r,m}(n - 3j(j+1)/2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, G(n - mj - r).$$

The sum on the left starts at $j = 1$. Starting it at $j = 0$ makes the identity false: for
$m = 1$, $r = 0$ and $n = 1$ the left side becomes $-a_{0,1}(1) = -1$ while the right side is $0$.

## Sources

- Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024), Article A15, Theorem 10 (i) (`integers-2024-A15-thm-10`).
