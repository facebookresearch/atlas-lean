# Deletion from a doubly linked list allocates and frees nothing

Let $S$ be a store of $n$
cells, each empty or holding a node (a payload with next and previous pointers, each an index or
NIL), let $h$ be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose
cell holds a node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Let $S'$ be the store returned
by List Delete on $S$, $h$ and $x$. Then for every index $z$, the cell $S'(z)$ holds a node if and
only if $S(z)$ does.
