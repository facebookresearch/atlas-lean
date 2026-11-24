# Executable mutual-reachability test

For a directed graph $G$ and vertices $u$ and $v$, the
test returns true exactly when $v$ occurs in the preorder of the depth-first search of $G$ from
the single root $u$, and $u$ occurs in the preorder of the depth-first search of $G$ from the
single root $v$.
