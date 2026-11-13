# Splay operation

Let $\alpha$ be a linearly ordered type and write $(k; L, R)$ for the binary
tree with root key $k$, left subtree $L$ and right subtree $R$. For $x \in \alpha$, the splay
$S_x(t)$ of a binary tree $t$ with keys in $\alpha$ is defined by recursion on $t$. The empty tree
splays to itself, and $t = (k; L, R)$ is left unchanged if $x = k$, if $x < k$ and $L$ is empty,
or if $x > k$ and $R$ is empty. If $x < k$ and $L = (a; A, B)$, then: if $x = a$, the result is
the zig $(a; A, (k; B, R))$; if $x < a$ and $S_x(A) = (d; A_1, A_2)$, the result is the zig-zig
$(d; A_1, (a; A_2, (k; B, R)))$; if $x > a$ and $S_x(B) = (d; B_1, B_2)$, the result is the
zig-zag $(d; (a; A, B_1), (k; B_2, R))$; and if the splayed subtree $S_x(A)$, respectively
$S_x(B)$, is empty, the result is the zig $(a; A, (k; B, R))$. The case $x > k$ with
$R = (b; C, D)$ is the mirror image: if $x = b$, the result is the zig $(b; (k; L, C), D)$; if
$x > b$ and $S_x(D) = (d; D_1, D_2)$, it is the zig-zig $(d; (b; (k; L, C), D_1), D_2)$; if
$x < b$ and $S_x(C) = (d; C_1, C_2)$, it is the zig-zag $(d; (k; L, C_1), (b; C_2, D))$; and if
the splayed subtree is empty, it is the zig $(b; (k; L, C), D)$.

The search path for $x$ runs from the root to the node with key $x$, or to the last node visited
if $x$ is absent. Each recursive step consumes two edges of this path, starting at the root, so
when the path has an odd number of edges the single rotation is performed on its last edge, the
one farthest from the root.
