# Correctness of the Treiber stack

A concurrent history of operation invocations and responses is *linearizable* with respect to a sequential specification if it can be
completed and reordered into a legal sequential history of the specification that preserves the real-time order of non-overlapping
operations. An implementation is linearizable if all its histories are. An implementation is *lock-free* if every infinite
execution contains infinitely many completed operations.

Treiber's stack keeps a pointer to the top node of a singly linked list. A push allocates a node, reads the top pointer, links the node to
it and installs the node with a compare-and-swap on the top pointer, retrying if the compare-and-swap fails. A pop reads the top pointer,
returns empty if it is null, and otherwise installs the successor of the top node by compare-and-swap, retrying on failure.

This node covers the correctness of Treiber's stack: its linearizability with respect to the sequential stack specification and its
lock-freedom, under sequential consistency, with an atomic compare-and-swap on the top pointer and with nodes never reused, so that
the ABA problem cannot occur. A precise statement fixes the shared-memory semantics and states both properties against a checked source.

## Expansion

This page becomes ready once these prerequisites are stated:

- Linearizability of operation histories (statement prerequisite).
- Progress conditions for concurrent implementations, including lock-freedom (statement prerequisite).
- A shared-memory semantics with atomic reads, writes and compare-and-swap in which the algorithm is expressed.

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, <https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf>: Section 2 (histories, completion and the definition of linearizability).
- R. K. Treiber, *Systems Programming: Coping with Parallelism*, Technical Report RJ 5118, IBM Almaden Research Center, 1986.
- M. Herlihy and N. Shavit, *The Art of Multiprocessor Programming*, revised ed., Morgan Kaufmann, 2012.
