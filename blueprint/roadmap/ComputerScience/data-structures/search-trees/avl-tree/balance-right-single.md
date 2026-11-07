# Single left rotation in AVL rebalancing

Write $h(T)$ for the cached height at the root of
a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with cached height
$c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $L$, $A$, $B$ be trees with cached heights,
let $x$, $y$ be keys and let $c$ be a natural number. If $h(L) + 1 < c$ and $h(A) \le h(B)$, then
$\mathrm{balance}(L, x, \langle c; A, y, B \rangle) = N(N(L, x, A), y, B)$.
