# Correct cached heights

The empty tree has correct cached heights. A node storing the
height $c$, with left subtree $\ell$ and right subtree $r$, has correct cached heights when
$\ell$ and $r$ have correct cached heights and $c = \max(h(\ell), h(r)) + 1$, where $h$ denotes
the height cached at the root of a tree (and $0$ for the empty tree).
