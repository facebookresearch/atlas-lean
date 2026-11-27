# Amplifying the LSH success probability by repetition

Build $t$ independent copies of the LSH index and answer a query by querying the copies in turn and returning the first answer found. Every returned answer is still within distance $cr$ of the query, and if a single copy fails with probability at most $f$ on a query with a point within distance $r$, the combined structure fails with probability at most $f^t$; with the standard parameters $f \le e^{-1} + 1/3 < 0.71$, so $t = O(\log(1/\delta))$ copies give failure probability at most $\delta$.

## Proof sketch

The copies use independent seeds, so the failure events are independent, and each answer is checked against the distance threshold before being returned.

## Depends on

- [Locality-sensitive hashing index with L tables and a stopping rule](lsh-index.md)

## Proof depends on

- [Failure probability of the LSH index](failure-probability-of-the-lsh-index.md)

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
