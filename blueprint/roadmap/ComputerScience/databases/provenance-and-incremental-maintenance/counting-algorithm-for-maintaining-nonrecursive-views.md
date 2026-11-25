# Counting algorithm for maintaining nonrecursive views

Let $V$ be a view defined by a nonrecursive, aggregation-free query built from selection, projection,
join and union, evaluated under bag semantics on a database whose relations have nonnegative
multiplicities. Store with each tuple of $V$ its multiplicity (its number of derivations). An update is a
signed change of base multiplicities whose result is again nonnegative. Computing the signed change
of $V$ by the delta rules and adding it to the stored counts yields exactly the multiplicities of $V$ on
the updated database, and a tuple belongs to the set-semantics view if and only if its count is
positive. Signed deltas are used only as updates, never as database states with negative
multiplicities.

## Depends on

- [Bag relations and bag relational algebra](../bags-and-nulls/bag-relations-and-bag-relational-algebra.md)
- [Z-relations and delta rules for incremental maintenance](z-relations-and-delta-rules-for-incremental-maintenance.md)

## Sources

- Maintaining Views Incrementally (Gupta, Mumick, Subrahmanian), SIGMOD 1993, Section 4, Algorithm 4.1, Lemma 4.1 (deletions a subset of the old database) and Theorem 4.1 (the derived change of each count is the new count minus the old). <http://www.cs.columbia.edu/~gravano/Qual/Papers/13%20-%20Maintaining%20Views%20Incrementally.pdf>
