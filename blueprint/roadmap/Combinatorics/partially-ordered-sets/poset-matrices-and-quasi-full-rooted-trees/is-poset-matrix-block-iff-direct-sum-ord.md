# Block decomposition of a poset matrix

Let $m, k \ge 1$ and let $M$ be a poset matrix of
order $m + k$, a Boolean matrix with rows and columns indexed by $0, \dots, m + k - 1$. Then
$M_{ij}$ is false for all $i < m \le j$ if and only if there are poset matrices $A$ of order $m$
and $B$ of order $k$ such that $M$ is their direct sum: $M_{ij} = A_{ij}$ for $i, j < m$,
$M_{m+i, m+j} = B_{ij}$ for $i, j < k$, and every other entry of $M$ is false. Likewise $M_{ij}$
is true for all $i < m \le j$ if and only if there are poset matrices $A$ of order $m$ and $B$ of
order $k$ such that $M$ is their ordinal sum: the same diagonal blocks, $M_{ij}$ true for all
$i < m \le j$, and $M_{ij}$ false for all $j < m \le i$.

Only one block length is stated; the version with several lengths $n_1 < \dots < n_r$ follows by
iterating it.

## Sources

- Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025), Article 25.6.3, Theorem 3 (`jis-2025-25.6.3-thm-3`).
