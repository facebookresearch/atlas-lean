# Point update preserves representation

Let $t$ be a Fenwick tree over an additive
commutative monoid that represents a list $a$ of length $n$. For every index $i < n$ (counting
from $0$) and every element $\delta$, the tree obtained from $t$ by adding $\delta$ at position
$i$ represents the list obtained from $a$ by replacing its entry $a_i$ with $a_i + \delta$.
