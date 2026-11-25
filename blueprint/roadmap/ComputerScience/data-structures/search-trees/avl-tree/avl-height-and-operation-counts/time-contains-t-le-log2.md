# Logarithmic operation count for AVL search

Let the keys be linearly ordered and let $t$ be a binary tree with cached heights (each node stores a natural number, its cached height, besides its left subtree, key and right subtree). Write $h(t)$ for the height cached at the root of $t$, with $h$ of the empty tree equal to $0$. Suppose its cached heights are correct (every node stores $\max(h(\ell), h(r)) + 1$ for its subtrees $\ell$ and $r$, recursively) and it is balanced (at every node the cached heights of the two subtrees differ by at most one), and let $n$ be the number of keys of $t$. Then for every key $x$ the cost of counted search for $x$ in $t$ is at most

$$6 \left( \lfloor \log_2 (n + 1) \rfloor + 1 \right),$$

where $\lfloor \log_2 \cdot \rfloor$ is the natural-number base-2 logarithm rounded down. No order hypothesis is needed.

In this operation-count model one unit is charged for each visit to a nonempty node in a recursive traversal, each executed key comparison ($<$), each inspection of a nonempty heavy child or inner grandchild during rebalancing, and each node rebuild; reading and comparing cached heights, arithmetic on them, pattern matching, recursive calls themselves and returning existing subtrees cost nothing. The count is not CPU time or Turing-machine time.
