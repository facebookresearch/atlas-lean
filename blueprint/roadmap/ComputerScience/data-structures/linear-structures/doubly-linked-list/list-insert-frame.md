# Frame property of doubly-linked-list insertion

For a store $S$ and allocated cells $x$
and $y$ such that the successor of $y$ in $S$, if any, is allocated, let $z$ be a cell with
$z \ne x$, $z \ne y$, and $z$ not the successor of $y$ in $S$. Then cell $z$ of the store
returned by inserting $x$ after $y$ equals cell $z$ of $S$.
