# Different parts in a residue class and even-minus-odd partition counts

Let $m$, $r$ and
$n$ be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $p_{e-o}(k) = \sum_{\mu} (-1)^{\ell(\mu)}$, the sum over
the partitions $\mu$ of $k$ with $\ell(\mu)$ the number of parts of $\mu$; it is the number of
partitions of $k$ with an even number of parts minus the number with an odd number of parts. Then

$$a_{r,m}(n) + 2 \sum_{k \ge 1,\ k^2 \le n} (-1)^k a_{r,m}(n - k^2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, p_{e-o}(n - mj - r).$$

## Sources

- Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024), Article A15, Theorem 2 (`integers-2024-A15-thm-2`).
