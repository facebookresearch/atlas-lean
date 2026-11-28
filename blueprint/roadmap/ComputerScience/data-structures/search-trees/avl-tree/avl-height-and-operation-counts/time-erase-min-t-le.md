# Removing the leftmost key costs at most six units per level

Let $t$ be a binary tree with cached heights (each node stores a natural number, its cached height, besides its left subtree, key and right subtree). Write $h(t)$ for the height cached at the root of $t$, with $h$ of the empty tree equal to $0$. If its cached heights are correct (every node stores $\max(h(\ell), h(r)) + 1$ for its subtrees $\ell$ and $r$, recursively), then the cost of counted removal of the leftmost key of $t$ is at most

$$6\,h(t).$$

No balance or order hypothesis is needed.

In this operation-count model one unit is charged for each visit to a nonempty node in a recursive traversal, each executed key comparison ($<$), each inspection of a nonempty heavy child or inner grandchild during rebalancing, and each node rebuild; reading and comparing cached heights, arithmetic on them, pattern matching, recursive calls themselves and returning existing subtrees cost nothing. The count is not CPU time or Turing-machine time.
