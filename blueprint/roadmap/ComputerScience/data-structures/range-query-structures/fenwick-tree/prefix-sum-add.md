# Prefix sums after a point update

Let $t$ be a Fenwick tree representing a list $a$ of
elements of an additive commutative monoid, let $i < |a|$ be a position, let $\delta$ be an
element of the monoid, and let $k$ be any natural number, possibly larger than $|a|$. Then the
prefix sum of length $k$ of the tree obtained from $t$ by adding $\delta$ at position $i$ equals
the prefix sum of length $k$ of $t$ plus $\delta$ if $i < k$, and equals the prefix sum of
length $k$ of $t$ if $k \le i$.
