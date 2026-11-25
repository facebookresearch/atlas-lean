# Fibonacci lower bound on the size of an AVL tree

Let $t$ be a binary tree with cached heights (each node stores a natural number, its cached height, besides its left subtree, key and right subtree). Write $h(t)$ for the height cached at the root of $t$, with $h$ of the empty tree equal to $0$. Suppose its cached heights are correct (every node stores $\max(h(\ell), h(r)) + 1$ for its subtrees $\ell$ and $r$, recursively) and it is balanced (at every node the cached heights of the two subtrees differ by at most one). Let $n$ be the number of keys of $t$ and let $F$ be the Fibonacci sequence with $F_0 = 0$, $F_1 = 1$ and $F_{m+2} = F_{m+1} + F_m$. Then

$$F_{h(t) + 2} \le n + 1,$$

that is, $t$ has at least $F_{h(t)+2} - 1$ keys.
