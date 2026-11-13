# Optimality of exact subset sum for distinct positive inputs

Let $x$ be a list of
distinct positive natural numbers, $t$ a positive natural number, and $r$ the value returned by
the exact subset sum algorithm on $x$ with target $t$. Then $r$ is the sum of some sublist of
$x$ (a subsequence, not necessarily contiguous), $r \le t$, and every sublist of $x$ whose sum
is at most $t$ has sum at most $r$.

These are the hypotheses of CLRS, Section 35.5; the proof does not use them.
