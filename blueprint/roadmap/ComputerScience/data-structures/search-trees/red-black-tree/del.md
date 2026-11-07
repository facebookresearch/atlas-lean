# Unbalanced red-black tree deletion

For a key $x$ of a linearly ordered type, unbalanced
deletion of $x$ from a red-black tree is defined by recursion on the tree. The empty tree stays
empty. At a node with color $c$, left subtree $l$, key $k$ and right subtree $r$: if $x < k$, the
result is the node with color $c$, left subtree the unbalanced deletion of $x$ from $l$, key $k$
and right subtree $r$; if $k < x$, it is the node with color $c$, left subtree $l$, key $k$ and
right subtree the unbalanced deletion of $x$ from $r$; otherwise (so $x = k$) it is the splice of
$l$ with $r$.

Colors are kept, so the result need not satisfy the red invariant or be black-height balanced.
