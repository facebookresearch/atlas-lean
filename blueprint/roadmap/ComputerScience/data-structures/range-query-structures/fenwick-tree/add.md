# Point update of a Fenwick tree

Let $t$ be a Fenwick tree over a commutative additive
monoid $\alpha$, let $n$ be its size (the length of its stored array minus one), let $i$ be a
natural number and let $\delta \in \alpha$. Adding $\delta$ at underlying position $i$ adds
$\delta$ to the stored entries at the one-indexed positions $j_1 = i + 1$ and
$j_{k+1} = j_k + \operatorname{lowbit}(j_k)$, for as long as $j_k \le n$, where
$\operatorname{lowbit}(j)$ is the largest power of two dividing $j$; every other stored entry
is left unchanged. In particular, if $i \ge n$ the tree is unchanged.

Each write is constant-time only when the stored array is uniquely referenced, since a shared
array is copied by the first persistent write. The walk is fuelled by the size, which always
suffices because the visited positions strictly increase.
