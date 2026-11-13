# The memoized auxiliary preserves known and higher cache entries

Let $\alpha$ be an additive
commutative monoid with a linear order, let $p \in \alpha^n$ be a vector of prices, let
$c = (c_0, \dots, c_n)$ be a cache whose entries are each unknown or a value in $\alpha$, let
$j \le n$, and let $c'$ be the cache returned by the memoized rod-cutting auxiliary on length $j$
and cache $c$. Then for every $k \le n$, if $c_k$ is a known value $v$, then $c'_k = v$; and for
every $k$ with $j < k \le n$, $c'_k = c_k$.
