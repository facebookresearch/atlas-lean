# Linearizations respecting real-time order

A concurrent history is a list of completed operations, each recording its object, operation, argument, return value and the positions of its invocation and response in the global event order. A sequence of operations respects the real-time order when no operation responds before the invocation of an operation listed earlier.

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12 (1990), 463-492.
