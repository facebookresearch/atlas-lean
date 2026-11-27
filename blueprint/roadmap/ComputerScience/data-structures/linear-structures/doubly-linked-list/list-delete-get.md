# Cellwise result of doubly linked list deletion

Let $S$ be a store of $n$ cells, each
empty or holding a node (a payload with next and previous pointers, each an index or NIL), let $h$
be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a
node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Let $S'$ be the store returned
by List Delete on $S$, $h$ and $x$. For an index $z$, let $C$ be the cell $S(z)$ with the next
pointer of its node set to $X.\mathrm{next}$ if $X.\mathrm{prev} = z$, and $C = S(z)$ otherwise.
Then $S'(z)$ is $C$ with the previous pointer of its node set to $X.\mathrm{prev}$ if
$X.\mathrm{next} = z$, and $S'(z) = C$ otherwise; an empty cell stays empty. So the write at the
predecessor is applied before the write at the successor.
