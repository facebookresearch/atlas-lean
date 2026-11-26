# Uniform cost bound for doubly linked list prepend

Let a store assign to each identity
below $n$ either nothing or a doubly linked list node, let the head be an identity below $n$ or
NIL, and let $x$ be an identity whose store entry is a node, where the store entry of the head is
also a node when the head is not NIL. Then prepending $x$ costs at most $5$ time units, counting
one unit per pointer assignment and per NIL test of the old head.
