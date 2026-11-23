# Result of doubly-linked-list insertion

For a store $S$ and allocated cells $x$ and $y$
such that the successor of $y$ in $S$, if any, is allocated, let $s$ be the next pointer of $y$
in $S$. Let $S_1$ be $S$ with cell $x$ replaced by the node of $x$ with next pointer $s$ and
previous pointer $y$. Let $S_2 = S_1$ if $s$ is NIL; if $s$ is a cell $z$, let $S_2$ be $S_1$
with the previous pointer of the node in cell $z$ of $S_1$ replaced by $x$. Then the store
returned by inserting $x$ after $y$ is $S_2$ with the next pointer of the node in cell $y$ of
$S_2$ replaced by $x$.

No distinctness or representation hypothesis is assumed.
