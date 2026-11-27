# The memoized auxiliary fills the cache up to the requested length

Let $\alpha$ be a
linearly ordered additive commutative monoid (that is, $a \le b$ implies $a + c \le b + c$), let
$p = (p_1, \dots, p_n) \in \alpha^n$ be prices, where $p_i$ is the price of a piece of length $i$,
and let $j \le n$. If the memoized rod-cutting auxiliary is run on length $j$ with the cache
$(c_0, \dots, c_n)$ whose entries are all unknown, then for every $k \le j$ entry $k$ of the
returned cache is a known value, and that value is the greatest composition revenue over
compositions of $k$.
