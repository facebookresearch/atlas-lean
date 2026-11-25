# Linearizability

Fix a sequential specification for each object. A sequential history $S$ is *legal* if, for every object $x$, the object subhistory $S|x$ belongs to the sequential specification of $x$. A well-formed history $H$ is *linearizable* if it can be extended, by appending zero or more response events, to a history $H'$ such that $\mathrm{complete}(H')$ is equivalent to some legal sequential history $S$ and the real-time order of $\mathrm{complete}(H')$ is contained in that of $S$: $<_{\mathrm{complete}(H')} \subseteq <_S$. Such an $S$ is a *linearization* of $H$.

Appending responses lets a pending invocation take effect before its response is returned, and passing to $\mathrm{complete}(H')$ discards the pending invocations that have not taken effect. For histories without pending invocations this is the notion of [linearizable histories](../linearizability/linearizable.md) for completed operations, which this page extends.

## Depends on

- [Linearizable histories](../linearizability/linearizable.md)
- [Concurrent histories](concurrent-histories.md)
- [Prefix-closed and total sequential specifications](sequential-specifications-of-objects.md)

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, Section 2
