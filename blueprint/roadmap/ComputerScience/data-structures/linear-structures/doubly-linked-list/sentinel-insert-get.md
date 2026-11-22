# Sentinel insertion, cell by cell

Let $S$ be a store of $n$ cells, each empty or holding a
node, in which the cells $x$ and $y$ are allocated, the next pointer of $y$ is not NIL, and the
cell it points to is allocated; write $S[c]$ for the node at an allocated cell $c$. Let $S'$ be
the store returned by sentinel insertion of $x$ after $y$. Then for every cell $z$, the content of
$z$ in $S'$ is obtained from its content in $S$ by three steps in order: if $z = x$, replace the
content by the node $S[x]$ with next pointer equal to the next pointer of $S[y]$ and previous
pointer $y$; if the next pointer of $S[y]$ is $z$, set the previous pointer to $x$; if $z = y$,
set the next pointer to $x$. The last two steps leave an empty cell empty.

No distinctness of $x$, $y$, $z$ and the successor of $y$ is assumed.
