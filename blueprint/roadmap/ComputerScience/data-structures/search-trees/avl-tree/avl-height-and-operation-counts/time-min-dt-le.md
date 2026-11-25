# Leftmost-key search costs at most the height

Let $t$ be a binary tree with cached heights (each node stores a natural number, its cached height, besides its left subtree, key and right subtree). Write $h(t)$ for the height cached at the root of $t$, with $h$ of the empty tree equal to $0$. If its cached heights are correct (every node stores $\max(h(\ell), h(r)) + 1$ for its subtrees $\ell$ and $r$, recursively), then for every default key $d$ the cost of counted leftmost-key search in $t$ with default $d$, one unit per nonempty node visited, is at most $h(t)$.
