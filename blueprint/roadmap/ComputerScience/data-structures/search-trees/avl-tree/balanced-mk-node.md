# The AVL node constructor preserves balance

Let $\ell$ and $r$ be AVL trees that satisfy
the AVL balance invariant, and write $h(\ell)$ and $h(r)$ for the heights cached at their roots
(with height $0$ for the empty tree). If $h(\ell) \le h(r) + 1$ and $h(r) \le h(\ell) + 1$, then
for every key $k$ the node built from $\ell$, $k$ and $r$ by the smart constructor, which stores
the height $\max(h(\ell), h(r)) + 1$, satisfies the AVL balance invariant.
