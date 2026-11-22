# Optimality of exact subset sum

Let $x$ be a list of natural numbers, $t$ a natural
number, and $r$ the value returned by the exact subset sum algorithm on $x$ with target $t$.
Then $r$ is the sum of some sublist of $x$ (a subsequence, not necessarily contiguous),
$r \le t$, and every sublist of $x$ whose sum is at most $t$ has sum at most $r$.

The entries of $x$ may be zero or repeated.
