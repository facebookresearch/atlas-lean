# Prefix-closed and total sequential specifications

A [sequential specification](../linearizability/seq-spec.md) is *prefix-closed* if every prefix of a legal sequence is legal; the sequential specification of an object is usually a prefix-closed set of single-object sequential histories of that object, finite sequences of operations with their arguments and results, usually given by a state machine with an initial state and, for each operation, a transition relation on states and results. An operation is *total* if it is defined for every value of the object, that is, it has a legal result in every state; otherwise it is *partial*, like dequeuing from an empty queue.

## Depends on

- [Concurrent histories](concurrent-histories.md)
- [Sequential specifications](../linearizability/seq-spec.md)

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, Section 2.1
