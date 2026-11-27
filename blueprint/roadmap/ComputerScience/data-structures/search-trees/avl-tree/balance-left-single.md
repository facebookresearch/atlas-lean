# Single right rotation in AVL rebalancing

Write $h(T)$ for the cached height at the root
of a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with cached
height $c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $A$, $B$, $R$ be trees with cached heights,
let $x$, $y$ be keys and let $c$ be a natural number. If $h(R) + 1 < c$ and $h(B) \le h(A)$, then
$\mathrm{balance}(\langle c; A, y, B \rangle, x, R) = N(A, y, N(B, x, R))$.
