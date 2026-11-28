# Counted removal of the leftmost key of an AVL tree

For a binary tree $t$ with cached heights, counted removal of the leftmost key returns a tree together with a natural-number cost. On the empty tree it returns the empty tree at cost $0$. At a node with left subtree $L$, key $k$ and right subtree $R$, it charges $1$ for visiting the node; if $L$ is empty it returns $R$ with no further cost, and otherwise counted removal of the leftmost key of $L$ yields $L'$ and the result is counted rebalancing of $L'$, $k$, $R$, with both costs added.

In this operation-count model one unit is charged for each visit to a nonempty node in a recursive traversal, each executed key comparison ($<$), each inspection of a nonempty heavy child or inner grandchild during rebalancing, and each node rebuild; reading and comparing cached heights, arithmetic on them, pattern matching, recursive calls themselves and returning existing subtrees cost nothing. The count is not CPU time or Turing-machine time.
