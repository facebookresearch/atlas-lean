# A cache hit in memoized rod cutting returns at once

Let $\alpha$ be an additive commutative
monoid with a linear order, let $p \in \alpha^n$ be a vector of prices, let $c = (c_0, \dots, c_n)$
be a cache whose entries are each unknown or a value in $\alpha$, and let $j \le n$. If $c_j$ is a
known value $v$, then the memoized rod-cutting auxiliary on length $j$ and cache $c$ returns $v$
and the unchanged cache $c$, and charges exactly one event.
