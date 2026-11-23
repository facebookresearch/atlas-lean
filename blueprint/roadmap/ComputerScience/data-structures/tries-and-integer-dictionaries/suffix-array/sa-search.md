# Suffix-array search for a pattern's row interval

Let $s$ and $P$ be lists over a linear order, $n$ the length of $s$ and $A$ the suffix array of
$s$. For a row $r$, let $k(r)$ be the key of row $r$ in $A$ truncated to the length of $P$. The
suffix-array search returns the pair $(sp, ep)$, where $sp$ is the result of the binary search on
$0, n$ for the test "$k(r) < P$" and $ep$ is the result of the binary search on $0, n$ for the test
"$k(r) \le P$", both in the lexicographic order. The suffix array is computed once and shared by
both searches. This is the search of Manber and Myers (1993).
