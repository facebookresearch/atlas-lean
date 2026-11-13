# Output of naive matching

Let $p$ be a pattern of length $m$ and $t$ a text of length
$n$. If $m \le n$, the list of shifts reported by the naive matcher on $p$ and $t$ is the
increasing list of all $s \in \{0, \dots, n - m\}$ such that $p$ is a prefix of the suffix of
$t$ starting at the zero-based position $s$, with symbols compared by the Boolean equality of the
alphabet. If $m > n$, the list is empty.
