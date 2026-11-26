# Well-formed concurrent histories

A concurrent history is a list of completed operations, each recording its object, operation, argument, return value and the positions of its invocation and response in the global event order. A history is well formed when the invocation and response positions of all its operations, listed operation by operation, are pairwise distinct; in particular no operation occurs twice.

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12 (1990), 463-492.
