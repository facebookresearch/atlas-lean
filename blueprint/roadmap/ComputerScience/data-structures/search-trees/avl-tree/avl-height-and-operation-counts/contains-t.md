# Counted AVL search

Let the keys be linearly ordered and let $x$ be a key. Counted search for $x$ returns a Boolean together with a natural-number cost. On the empty tree it returns false at cost $0$. At a node with key $k$, left subtree $L$ and right subtree $R$, it charges $1$ for visiting the node and $1$ for the comparison $x < k$; if $x < k$ it continues with counted search in $L$. Otherwise it charges $1$ more for the comparison $k < x$, continues with counted search in $R$ if $k < x$, and otherwise returns true. Costs along the path are added, and cached heights are ignored.
