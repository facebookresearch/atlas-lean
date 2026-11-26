# AVL rebalancing

For trees $l$, $r$ with cached heights and a key $x$, write $h(T)$ for
the cached height at the root of a tree $T$ (zero for the empty tree) and $N(A, y, B)$ for the
node with left subtree $A$, key $y$, right subtree $B$ and cached height $\max(h(A), h(B)) + 1$.
The node $\mathrm{balance}(l, x, r)$ is defined by cases. If $h(l) > h(r) + 1$ and $l$ has left
subtree $A$, key $y$ and right subtree $B$, it is the single right rotation $N(A, y, N(B, x, r))$
when $h(B) \le h(A)$, and otherwise, when $B$ has left subtree $B_1$, key $z$ and right subtree
$B_2$, the left-right double rotation $N(N(A, y, B_1), z, N(B_2, x, r))$. Symmetrically, if
$h(l) \le h(r) + 1$, $h(r) > h(l) + 1$ and $r$ has left subtree $A$, key $y$ and right subtree $B$,
it is the single left rotation $N(N(l, x, A), y, B)$ when $h(A) \le h(B)$, and otherwise, when
$A$ has left subtree $A_1$, key $z$ and right subtree $A_2$, the right-left double rotation
$N(N(l, x, A_1), z, N(A_2, y, B))$. In every other case it is $N(l, x, r)$.

For balanced children with correct cached heights whose heights differ by at most two, the result
is balanced again.
