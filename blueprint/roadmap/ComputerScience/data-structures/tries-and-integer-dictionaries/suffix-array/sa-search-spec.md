# Suffix-array search is correct

Let $s$ and $P$ be lists over a linear order, $n$ the length of $s$, and $(sp, ep)$ the pair
returned by the suffix-array search for $P$ in $s$. For every row $r < n$, we have
$sp \le r < ep$ if and only if $P$ is a prefix of the suffix of $s$ starting at the entry at
position $r$ of the suffix array of $s$.
