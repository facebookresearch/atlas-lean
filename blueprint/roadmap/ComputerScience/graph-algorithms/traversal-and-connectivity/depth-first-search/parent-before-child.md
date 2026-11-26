# In preorder, a DFS parent precedes its child

Let $G$ be a finite directed graph and $R$ a
list of root vertices, and run depth-first search on $G$ from $R$. If the pair $(c, p)$ occurs in
the list of (child, parent) pairs recorded by the search, then $p$ occurs strictly before $c$ in
the discovery order (preorder) of the search.
