# Red-black tree deletion by rebuilding

For a key $x$ of a linearly ordered type and a
red-black tree $t$, deleting $x$ from $t$ by rebuilding first forms the unbalanced deletion of
$x$ from $t$, then rebalances it: starting from the empty tree, it inserts the keys of the inorder
traversal of that tree one at a time, from the last key to the first.
