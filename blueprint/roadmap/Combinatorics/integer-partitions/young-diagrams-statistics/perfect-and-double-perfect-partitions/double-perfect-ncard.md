# Lee's count of double-perfect partitions

Let $f(m)$ be the number of ordered
factorizations of $m$ into factors greater than $1$, with $f(0) = 0$ and $f(1) = 1$. For every
$n \ge 4$, the number $d(n)$ of double-perfect partitions of $n$ of order $1$ is $f(n-1)$ unless
$n \equiv 1 \pmod 4$, in which case $d(n) = f(n-1) - f((n-1)/4)$.

The hypothesis $n \ge 4$ is needed: for $n = 3$ both perfect partitions $(1^3)$ and $(1, 2)$ are
double-perfect of order $1$ while $f(2) = 1$, and for $n = 1$ the partition $(1)$ is
double-perfect of order $1$ while $f(0) = 0$.

## Sources

- Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025), Article A109, Theorem 1 (Lee), display (4) (`integers-2025-A109-thm-1`).
