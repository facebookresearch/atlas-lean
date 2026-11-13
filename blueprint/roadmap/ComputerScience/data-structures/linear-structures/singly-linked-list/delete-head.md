# Deleting the head of a singly linked list

Let a store assign to each identity below $n$
either nothing or a singly linked list node whose next pointer is an identity below $n$ or NIL,
and let the head be an identity below $n$ or NIL. Deleting the head returns the store unchanged
together with a new head: NIL if the head is NIL or the store entry at the head is empty, and
otherwise the next pointer of the node stored at the head.
