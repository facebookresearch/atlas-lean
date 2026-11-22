# Right-left double rotation in AVL rebalancing

Write $h(T)$ for the cached height at the
root of a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with
cached height $c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $L$, $A$, $B$, $C$ be trees with cached
heights, let $x$, $y$, $z$ be keys and let $c$, $c'$ be natural numbers. If $h(L) + 1 < c$ and
$h(C) < c'$, then $\mathrm{balance}(L, x, \langle c; \langle c'; A, z, B \rangle, y, C \rangle) =
N(N(L, x, A), z, N(B, y, C))$.
