# Backward search is correct

Let $t = t_0 \cdots t_{n-1}$ be a text and $P$ a pattern over a linearly ordered alphabet, let
$t\bot$ be $t$ followed by a sentinel $\bot$ smaller than every letter, and let $[sp, ep)$ be the
interval returned by backward search for $P$ on the Burrows–Wheeler transform of $t$. For every
row $r \le n$, we have $sp \le r < ep$ if and only if $P$ is a prefix of row $r$ of the
Burrows–Wheeler matrix, that is, of the rotation of $t\bot$ that starts at the $r$-th entry of the
sorted rotations of $t$.
