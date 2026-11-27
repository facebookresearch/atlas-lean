# Left-right double rotation in AVL rebalancing

Write $h(T)$ for the cached height at the
root of a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with
cached height $c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $A$, $B$, $C$, $R$ be trees with cached
heights, let $x$, $y$, $z$ be keys and let $c$, $c'$ be natural numbers. If $h(R) + 1 < c$ and
$h(A) < c'$, then $\mathrm{balance}(\langle c; A, y, \langle c'; B, z, C \rangle \rangle, x, R) =
N(N(A, y, B), z, N(C, x, R))$.
