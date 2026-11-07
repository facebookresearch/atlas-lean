# Grafting a tree below a vertex

For a vertex $y$ and trees $N$ and $T$, grafting $N$ at
$y$ in $T$ attaches $N$ as a new last child of the first node of $T$ labelled $y$ in preorder,
keeping every existing node and edge; it returns nothing when $y$ does not occur in $T$. This is
the tree surgery behind linking two trees: it adds exactly the edge from $y$ to the root of $N$.
