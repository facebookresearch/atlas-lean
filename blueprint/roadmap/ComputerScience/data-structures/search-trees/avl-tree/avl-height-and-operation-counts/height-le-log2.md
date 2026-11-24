# Logarithmic height bound for AVL trees

Let $t$ be a binary tree with cached heights (each node stores a natural number, its cached height, besides its left subtree, key and right subtree). Write $h(t)$ for the height cached at the root of $t$, with $h$ of the empty tree equal to $0$. Suppose its cached heights are correct (every node stores $\max(h(\ell), h(r)) + 1$ for its subtrees $\ell$ and $r$, recursively) and it is balanced (at every node the cached heights of the two subtrees differ by at most one). Let $n$ be the number of keys of $t$. Then

$$h(t) \le 2 \lfloor \log_2 (n + 1) \rfloor + 1,$$

where $\lfloor \log_2 \cdot \rfloor$ is the natural-number base-2 logarithm rounded down.
