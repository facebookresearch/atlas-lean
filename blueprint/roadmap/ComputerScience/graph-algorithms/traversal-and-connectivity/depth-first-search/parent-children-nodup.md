# No vertex is recorded twice as a DFS child

Let $G$ be a finite directed graph and $R$ a
list of root vertices, and run depth-first search on $G$ from $R$. In the list of
(child, parent) pairs recorded by the search, no vertex occurs as the child of more than one
entry; that is, the list of children has no repeated entries.
