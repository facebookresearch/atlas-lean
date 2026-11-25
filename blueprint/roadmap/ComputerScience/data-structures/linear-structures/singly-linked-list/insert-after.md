# Inserting a node after another in a singly linked list

Let a store $S$ assign to each
identity below $n$ either nothing or a singly linked list node whose next pointer is an identity
below $n$ or NIL, and let $x$ and $y$ be identities whose store entries are nodes. Inserting $x$
after $y$ first replaces cell $x$ by the node of $x$ with next pointer replaced by the next
pointer of $y$ in $S$, then, in the store so obtained, replaces the next pointer of the node in
cell $y$ by $x$, and returns the resulting store.
