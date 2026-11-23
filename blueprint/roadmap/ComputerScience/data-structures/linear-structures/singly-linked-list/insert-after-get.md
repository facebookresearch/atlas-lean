# Cells after singly-linked-list insertion

Let $S$ be a store assigning to each identity
below $n$ either nothing or a singly linked list node, let $x$ and $y$ be identities whose store
entries are nodes, and let $z$ be any identity. Let $c$ be the node of $x$ in $S$ with next
pointer replaced by the next pointer of $y$ in $S$ if $z = x$, and the content of cell $z$ in $S$
otherwise. Then cell $z$ of the store obtained by inserting $x$ after $y$ is $c$ with next pointer
replaced by $x$ if $z = y$, and $c$ otherwise.

No distinctness of $x$ and $y$ is assumed.
