# Concurrent histories

A *history* is a finite list of invocation and response events, each tagged with a process and an object. An invocation carries an operation and its arguments; a response carries a termination condition and its results. The list order orders the event occurrences, even when their labels are identical.

A history is *sequential* if it consists of adjacent invocation–response pairs, each matching in process and object, followed by at most one unmatched invocation. It is *well formed* if every process subhistory is sequential. A process (or object) subhistory retains just the events of that process (or object), without changing their order. Object subhistories of a well-formed history need not be sequential.

A *completed operation* is an invocation and its next event at the same process when that next event is a response on the same object. An invocation with no such response is *pending*; in a well-formed history it must be last for its process, not necessarily last in the entire history. $\mathrm{complete}(H)$ deletes the pending invocations in $H$ and preserves the order of the remaining events. Two histories are *equivalent* if their process subhistories are equal, even when their global interleavings differ.

The *real-time order* $o_1 <_H o_2$ holds when the response of $o_1$ occurs before the invocation of $o_2$. Overlapping completed operations need not be comparable. The [completed-operation model](../linearizability/well-formed.md) retains the original event positions and this order, but does not record process identity and thus does not express equivalence of process subhistories.

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, Section 2
