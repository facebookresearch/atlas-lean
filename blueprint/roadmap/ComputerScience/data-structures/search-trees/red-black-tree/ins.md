# Unchecked red-black insertion

For keys from a linearly ordered type, the unchecked
insertion of $x$ into a red-black tree is defined by recursion on the tree. Inserting $x$ into the
empty tree gives a red node with key $x$ and two empty subtrees. Inserting $x$ into a node with
color $c$, left subtree $l$, key $k$ and right subtree $r$ gives: if $x < k$, Okasaki's
rebalancing of color $c$, left subtree the insertion of $x$ into $l$, key $k$ and right subtree
$r$; if $k < x$, Okasaki's rebalancing of color $c$, left subtree $l$, key $k$ and right subtree
the insertion of $x$ into $r$; otherwise the node itself, unchanged.

The result may have a red root with a red child, so it need not satisfy the red invariant.
