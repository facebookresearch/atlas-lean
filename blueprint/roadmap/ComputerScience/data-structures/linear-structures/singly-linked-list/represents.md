# Store representing a singly linked list

Fix a capacity $n$, let a store assign to each
identity below $n$ either nothing or a singly linked list node whose next pointer is an identity
below $n$ or NIL, and let the head be an identity below $n$ or NIL. The store and head represent
the list of identities $i_0, \dots, i_{k-1}$ when these identities are pairwise distinct, the head
is $i_0$ (and NIL when $k = 0$), and for each $j < k$ the store entry at $i_j$ is a node whose next
pointer is $i_{j+1}$ if $j + 1 < k$ and NIL otherwise.
