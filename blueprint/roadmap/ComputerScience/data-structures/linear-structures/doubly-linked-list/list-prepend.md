# Prepending a node to a doubly linked list

Let a store assign to each identity below $n$
either nothing or a doubly linked list node whose pointers are identities below $n$ or NIL, let
the head be an identity below $n$ or NIL, and let $x$ be an identity whose store entry is a node,
where the store entry of the head is also a node when the head is not NIL. The procedure sets the
next pointer of $x$ to the head, then sets the previous pointer of $x$ to NIL, then tests whether
the head is NIL; if it is not, it sets the previous pointer of the node at the head (read after
the two writes at $x$) to $x$. Finally it makes $x$ the new head and returns the updated store
together with the head $x$. One time unit is charged for each pointer assignment and for the NIL
test, so the cost is $4$ when the head is NIL and $5$ otherwise.
