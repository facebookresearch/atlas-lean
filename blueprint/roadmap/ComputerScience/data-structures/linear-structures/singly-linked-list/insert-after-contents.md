# Contents after singly-linked-list insertion

Let $S$ be a store assigning to each identity
below $n$ either nothing or a singly linked list node, let $(i_0, \dots, i_{m-1})$ be a list of
identities below $n$, let $k < m$, and let $x$ be an identity such that the store entries of $x$
and $i_k$ are nodes, the node of $x$ having payload $a$. Then the contents of the store obtained
by inserting $x$ after $i_k$ at the list $(i_0, \dots, i_k, x, i_{k+1}, \dots, i_{m-1})$ equal
the contents of $S$ at $(i_0, \dots, i_{m-1})$ with the present payload $a$ inserted as entry
$k + 1$ (counting from $0$).

No representation or distinctness hypothesis is assumed.
