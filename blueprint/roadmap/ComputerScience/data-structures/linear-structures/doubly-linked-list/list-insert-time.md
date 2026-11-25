# Cost of doubly-linked-list insertion

For a store $S$ and allocated cells $x$ and $y$
such that the successor of $y$ in $S$, if any, is allocated, the cost of inserting $x$ after
$y$, counting one unit per pointer assignment and per NIL test, is $5$ if $y$ has a successor
in $S$ and $4$ if the next pointer of $y$ in $S$ is NIL.

No distinctness of $x$ and $y$ is assumed.
