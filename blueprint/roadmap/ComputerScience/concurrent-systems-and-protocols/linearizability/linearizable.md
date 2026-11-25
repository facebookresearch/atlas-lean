# Linearizable histories

A concurrent history is a list of completed operations, each recording its object, operation, argument, return value and the positions of its invocation and response in the global event order. A history is linearizable against a sequential specification when it is well formed and some permutation of its operations respects the real-time order and, for every object $o$, lists the operations on $o$ as a sequence of (operation, argument, return value) triples that is legal for $o$.

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12 (1990), 463-492.
