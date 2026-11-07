# Block properties decide connectedness of the represented poset

Let $M$ be a poset matrix
of order $n$, a Boolean matrix with rows and columns indexed by $0, \dots, n - 1$, that
represents a partial order $P$: there is a bijection $e$ from $\{0, \dots, n - 1\}$ to $P$ such
that $e(i) \le e(j)$ if and only if $M_{ij}$ is true. Let $1 \le r < n$. If $M_{ij}$ is true for
all $i < r \le j$ (the block of $1$s property of length $r$), then $P$ is connected: every subset
$S$ of $P$ such that $x \in S \iff y \in S$ whenever $x \le y$ is empty or all of $P$. If
$M_{ij}$ is false for all $i < r \le j$ (the block of $0$s property of length $r$), then $P$ is
disconnected: some nonempty subset $S$ of $P$ with nonempty complement satisfies
$x \in S \iff y \in S$ whenever $x \le y$.

Since a relabeling of $M$ represents the same poset, this also covers matrices that satisfy a
block property after relabeling.

## Sources

- Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025), Article 25.6.3, Theorem 5 (`jis-2025-25.6.3-thm-5`).
