# Fenwick tree prefix sum

Let $t$ be a Fenwick tree over an additive commutative monoid
with $n$ underlying entries, let $k$ be a natural number and let $m = \min(k, n)$. The prefix sum
of length $k$ of $t$ is the sum of the stored entries of $t$ at the positions $j_0 = m$,
$j_{r+1} = j_r - \operatorname{lowbit}(j_r)$, taken for as long as $j_r > 0$.

When $t$ represents a list, this is the sum of its first $m$ entries, so queries past the end
are clamped.
