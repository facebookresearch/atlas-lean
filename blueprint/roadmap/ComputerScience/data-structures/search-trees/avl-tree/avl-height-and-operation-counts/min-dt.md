# Counted leftmost-key search in an AVL tree

For a default key $d$ and a binary tree $t$ with cached heights, counted leftmost-key search returns a key together with a natural-number cost. On the empty tree it returns $d$ at cost $0$. At a node with left subtree $L$ and key $k$, it charges $1$ for visiting the node and continues with counted leftmost-key search in $L$ with default $k$. So its cost is the number of nodes on the path from the root that follows left children as far as possible, and for a nonempty tree it returns the key at the end of that path.
