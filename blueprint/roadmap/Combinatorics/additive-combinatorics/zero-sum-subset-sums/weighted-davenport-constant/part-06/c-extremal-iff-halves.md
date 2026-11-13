# Halving consecutive unit-weighted zero-sum free sequences modulo a power of two

Let
$s \ge 0$, $n = 2^{s+1}$ and $n' = 2^s$. Say that a sequence $y_1, \dots, y_L$ in $\mathbb{Z}_m$ has
no consecutive unit-weighted zero-sum if there are no indices $1 \le i \le j \le L$ and units
$a_i, \dots, a_j$ of $\mathbb{Z}_m$ with $a_i y_i + \dots + a_j y_j = 0$. For a sequence
$x_1, \dots, x_{n-1}$ in $\mathbb{Z}_n$, let $r_l \in \{0, \dots, n - 1\}$ be the representative of
$x_l$ and let $\bar x_l \in \mathbb{Z}_{n'}$ be the residue of $\lfloor r_l / 2 \rfloor$. Then
$x_1, \dots, x_{n-1}$ has no consecutive unit-weighted zero-sum if and only if $r_l$ is even for
every $l \ne n'$, $r_{n'}$ is odd, and neither of the sequences $\bar x_1, \dots, \bar x_{n'-1}$
and $\bar x_{n'+1}, \dots, \bar x_{n-1}$ in $\mathbb{Z}_{n'}$ has a consecutive unit-weighted
zero-sum.

Write $U(n)$ for the unit group of $\mathbb{Z}_n$ and $C_{U(n)}(n)$ for the least positive $k$ such
that every sequence of length $k$ in $\mathbb{Z}_n$ has a consecutive unit-weighted zero-sum. Since
$C_{U(n)}(n) = n$, the sequences on the left are the $C$-extremal sequences for $U(n)$: those of
length $C_{U(n)}(n) - 1$ with no consecutive unit-weighted zero-sum.

## Sources

- Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.8.
