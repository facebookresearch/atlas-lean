# Cost of the FIND auxiliary at a root

Let $S$ be a union-find structure and $x < |S|$
a node. If the parent of $x$ in $S$ is $x$ itself, then the cost-counted FIND auxiliary on $x$
has cost $(1, 0)$: one root test and no parent writes.
