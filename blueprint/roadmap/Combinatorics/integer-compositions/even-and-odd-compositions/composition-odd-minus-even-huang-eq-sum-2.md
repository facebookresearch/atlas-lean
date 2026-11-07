# Signed count of Huang's compositions, monomial form

Let $k \ge 2$, $m \ge 0$ and
$n \ge 1$. Among the compositions of $n + k - 1$ with exactly $m$ parts less than $k$ in which
every part less than $k$ is preceded by a part at least $k$ and followed by a part that is either
the last part or greater than $k$, let $b^{(m)}_{k,n}$ be the number with an odd number of parts
minus the number with an even number of parts. Then $b^{(m)}_{k,n}$ is the sum of
$(-1)^j \binom{i}{m} \binom{i+j-1}{j}$ over all $i, j \ge 0$ and all functions
$g \colon \{1, \dots, m\} \to \{0, 1, \dots, k-2\}$ with
$i + (k+1)m + jk + g(1) + \dots + g(m) = n$, where $\binom{-1}{0} = 1$.

Grouping the functions $g$ by the partition $\lambda$ formed by their nonzero values gives the
paper's form of the sum: over partitions $\lambda$ with at most $m$ parts, each at most $k-2$
(written $\lambda \subseteq (k-2)^m$), of size $|\lambda| = n - i - (k+1)m - jk$, each weighted
by $m_\lambda(1^m)$, the monomial symmetric function $m_\lambda$ in $m$ variables evaluated at
$x_1 = \dots = x_m = 1$, which is the number of functions $g$ in the group.

## Sources

- Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal of Integer Sequences 27 (2024), Article 24.6.5, Theorem 16 (`jis-2024-24.6.5-thm-16`).
