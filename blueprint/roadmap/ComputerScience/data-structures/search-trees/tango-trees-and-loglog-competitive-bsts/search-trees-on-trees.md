# Search trees on trees

Let $G$ be a tree on $n$ vertices. A *search tree on $G$* is defined recursively: it is a rooted tree $S$ whose root is a vertex $r$ of $G$ and whose child subtrees are search trees on the connected components of $G - r$, one for each component. Searching for a vertex $v$ starts at the root of $S$ and costs the depth of $v$ in $S$; the dynamic model allows local rotations generalizing BST rotations, each of unit cost. When $G$ is a path, search trees on $G$ are exactly binary search trees.

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Prosenjit Bose, Jean Cardinal, John Iacono, Grigorios Koumoutsos, Stefan Langerman, "Competitive Online Search Trees on Trees", SODA (2020); ACM Transactions on Algorithms 19(3) (2023), arXiv:1908.00848.
