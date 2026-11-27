# Correctness of doubly linked list deletion

Let $S$ be a store of $n$ cells, each empty or
holding a node (a payload with next and previous pointers, each an index or NIL), let $h$ be a
header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node
$X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$
hold nodes whenever these pointers are not NIL. Let $S'$ and $h'$ be the store and header
returned by List Delete on $S$, $h$ and $x$. Let $L$ be a list of indices such that $S$ with
header $h$ represents $L$: the entries of $L$ are distinct, $h$ is the first entry of $L$ (NIL if
$L$ is empty), and the cell of each entry of $L$ holds a node whose previous and next pointers
are the adjacent entries of $L$, NIL at the ends. If $x$ is an entry of $L$, then $S'$ with
header $h'$ represents the list obtained from $L$ by removing $x$.
