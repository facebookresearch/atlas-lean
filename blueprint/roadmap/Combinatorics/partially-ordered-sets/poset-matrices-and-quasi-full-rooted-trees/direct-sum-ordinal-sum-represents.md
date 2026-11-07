# Direct and ordinal sums of poset matrices represent sums of posets

A poset matrix $M$ of
order $n$, a Boolean matrix with rows and columns indexed by $0, \dots, n - 1$, represents a
partial order $P$ when there is a bijection $e$ from $\{0, \dots, n - 1\}$ to $P$ such that
$e(i) \le e(j)$ if and only if $M_{ij}$ is true. Let $A$ and $B$ be poset matrices of orders $m$
and $k$ representing partial orders $P$ and $Q$. Let $A \oplus B$ and $A \boxplus B$ be the
matrices $N$ of order $m + k$ with $N_{ij} = A_{ij}$ for $i, j < m$, $N_{m+i, m+j} = B_{ij}$ for
$i, j < k$, and $N_{ij}$ false for all $j < m \le i$, where $N_{ij}$ for $i < m \le j$ is false
in $A \oplus B$ and true in $A \boxplus B$. Then $A \oplus B$ is a poset matrix representing the
disjoint sum $P + Q$, in which no element of $P$ is comparable with an element of $Q$, and
$A \boxplus B$ is a poset matrix representing the ordinal sum $P \oplus Q$, in which every
element of $P$ lies below every element of $Q$.

Only sums of two terms are stated; sums of $r$ terms follow by iterating.

## Sources

- Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025), Article 25.6.3, Theorem 4 (`jis-2025-25.6.3-thm-4`).
