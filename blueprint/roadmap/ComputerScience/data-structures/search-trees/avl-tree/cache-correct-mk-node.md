# The AVL node constructor preserves cached heights

If two AVL trees $\ell$ and $r$ have
correct cached heights, then for every key $k$ the node built from $\ell$, $k$ and $r$ by the
smart constructor, which stores the height $\max(h(\ell), h(r)) + 1$ where $h$ denotes the height
cached at the root (and $0$ for the empty tree), also has correct cached heights.
