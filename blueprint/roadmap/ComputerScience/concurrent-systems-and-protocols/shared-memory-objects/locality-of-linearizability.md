# Locality of linearizability

Let $H$ be a history of a concurrent system, a finite sequence of invocation and response events of operations on objects by processes. For an object $x$, write $H|x$ for the subsequence of events on $x$.

- **Well-formed histories.** $H$ is well-formed if the subhistory of each process is sequential: invocations and matching responses alternate.
- **Linearizability.** $H$ is linearizable if some extension of $H$, obtained by appending responses to pending invocations and then removing the remaining pending invocations, is equivalent to a legal sequential history $S$. Here $S$ must respect the real-time order of $H$: an operation that responds before another is invoked precedes it in $S$.

**Theorem (locality).** $H$ is linearizable if and only if $H|x$ is linearizable for every object $x$.

Hence a system built from linearizable objects is linearizable, and linearizability can be checked one object at a time, unlike sequential consistency or serializability.

**Proof.** The "only if" direction is immediate. Conversely, fix a linearization order $<_x$ of each $H|x$, and let $<$ be the transitive closure of the union of all $<_x$ with the real-time order $<_H$. It suffices to show that $<$ is a partial order; then any total order extending it gives the required sequential history. Suppose $<$ had a cycle, and take one of minimal length. If all its operations were on one object, the total order $<_x$ would contradict the linearizability of $H|x$. Otherwise, a case analysis using the minimality of the cycle and the transitivity of the real-time order yields a shorter cycle, a contradiction.

## Depends on

- [Concurrent histories](concurrent-histories.md)
- [Linearizability](linearizability.md)

## Proof depends on

- [Projections of linearizable histories are linearizable](../linearizability/linearizable-project.md)

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, <https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf>: Section 2 (histories, well-formed histories, complete histories and the definition of linearizability) and Section 3.1 (locality, Theorem 1 and its proof).
