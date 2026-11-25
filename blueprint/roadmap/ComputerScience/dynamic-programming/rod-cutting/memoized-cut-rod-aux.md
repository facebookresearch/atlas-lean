# Memoized rod-cutting auxiliary (CLRS MEMOIZED-CUT-ROD-AUX)

Let $\alpha$ be an additive
commutative monoid with a linear order, let $p = (p_1, \dots, p_n) \in \alpha^n$ be prices, where
$p_i$ is the price of a piece of length $i$, and let $c = (c_0, \dots, c_n)$ be a cache whose
entries are each either unknown or a value in $\alpha$. For $j \le n$ the procedure returns a value
and an updated cache, and counts events, as follows. It first charges one event for probing $c_j$.
If $c_j$ is a known value $v$, it returns $v$ and the unchanged cache $c$. Otherwise, if $j = 0$,
it charges one event for a write and returns $0$ with $c_0$ set to $0$. If $j \ge 1$, then for
$i = 1, \dots, j$ in turn it calls itself on length $j - i$ with the cache returned by the previous
call (starting from $c$), obtaining a value $q_i$, and charges one event for the candidate
$p_i + q_i$. It then charges one event for a write and returns
$q = \max(p_1 + q_1, \dots, p_j + q_j)$ with entry $j$ of the last returned cache set to $q$. The
event count is the total over the whole recursion.

Known entries are returned as they are, whatever their sign, including at length zero.
