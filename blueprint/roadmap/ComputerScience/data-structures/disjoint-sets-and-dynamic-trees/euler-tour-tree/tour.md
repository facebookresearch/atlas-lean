# Euler tour

The Euler tour of a tree $t$ with root $r$ and child subtrees
$c_1, \dots, c_k$ in order is the list of vertices consisting of $r$, followed, for each
$i = 1, \dots, k$ in turn, by the Euler tour of $c_i$ and then $r$. It is the vertex sequence of
the depth-first walk that returns to the parent vertex after each child subtree.
