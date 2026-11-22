# Counting occurrences

Let $t = t_0 \cdots t_{n-1}$ be a text and $P$ a pattern over a linearly ordered alphabet, and let
$[sp, ep)$ be the interval returned by backward search for $P$ on the Burrows–Wheeler transform of
$t$. Then $ep - sp$ is the number of positions $i$ with $0 \le i \le n$ such that $P$ is a prefix
of the suffix $t_i \cdots t_{n-1}$ of $t$ (the empty word when $i = n$).
