# The reported positions are exactly the occurrences

Let $t = t_0 \cdots t_{n-1}$ be a text and $P$ a pattern over a linearly ordered alphabet. A
natural number $i$ is among the occurrences of $P$ reported by the FM-index of $t$ if and only if
$i \le n$ and $P$ is a prefix of the suffix $t_i \cdots t_{n-1}$. In particular the empty pattern
is reported at all $n + 1$ positions.
