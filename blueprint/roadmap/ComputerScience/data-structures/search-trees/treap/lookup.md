# Treap lookup

Looking up a key $k$ in a tree with keys in a linearly ordered type follows
the binary search tree comparisons. The empty tree gives no value. At a node with key $r$ and
value $v$, the lookup continues in the left subtree if $k < r$, continues in the right subtree
if $r < k$, and otherwise returns $v$.
