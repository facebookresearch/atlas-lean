# Weight of the forest built from a parent array

Let $p$ be a parent array on the vertices
$\{0, \dots, n-1\}$, let $d$ be a cost on ordered pairs of vertices with values in an additive
commutative monoid, and let $\operatorname{up}(u)$ be the parent of $u$, or $u$ itself if $u$ has
no parent. For every $k \in \mathbb{N}$ and every vertex $v$, let $F$ be the forest of the subtrees
of the children of $v$ in $p$, cut off $k$ levels below $v$. Then the weight under $d$ of $F$
hanging below $v$ equals the sum of $d(\operatorname{up}(u), u)$ over the vertices $u$ of $F$ in
preorder.
