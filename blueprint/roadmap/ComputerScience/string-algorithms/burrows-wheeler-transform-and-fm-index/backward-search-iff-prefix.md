# Backward-search intervals are suffix-array intervals

Let $t = t_0 \cdots t_{n-1}$ be a text and $P$ a pattern over a linearly ordered alphabet, let
$t\bot$ be $t$ followed by a sentinel $\bot$ smaller than every letter, let $SA$ be the suffix
array of $t\bot$ (its positions $0, \dots, n$ sorted by their suffixes in lexicographic order), and
let $[sp, ep)$ be the interval returned by backward search for $P$ on the Burrows–Wheeler transform
of $t$. For every row $r \le n$, we have $sp \le r < ep$ if and only if $P$ is a prefix of the
suffix $t_{SA[r]} \cdots t_{n-1}$ of $t$.
