# Correctness of the memoized rod-cutting auxiliary

Let $\alpha$ be a linearly ordered
additive commutative monoid (that is, $a \le b$ implies $a + c \le b + c$) and let
$p = (p_1, \dots, p_n) \in \alpha^n$ be prices, where $p_i$ is the price of a piece of length $i$.
Call a cache $c = (c_0, \dots, c_n)$, whose entries are each unknown or a value in $\alpha$, valid
if for every known entry $c_k = v$ the value $v$ is the greatest composition revenue over
compositions of $k$. If $c$ is valid, $j \le n$, and the memoized rod-cutting auxiliary on length
$j$ and cache $c$ returns the value $q$ and the cache $c'$, then $q$ is the greatest composition
revenue over compositions of $j$, the cache $c'$ is valid, and $c'_j = q$.
