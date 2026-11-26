# The RANKING algorithm

In **online bipartite matching**, a finite set $L$ of offline vertices is known in advance; online vertices arrive one at a time, each revealing its set of neighbours in $L$, and must be matched irrevocably to an unmatched neighbour or left unmatched. **RANKING** draws a uniformly random permutation (rank order) of $L$ before any arrival and matches each arriving vertex to its unmatched neighbour of smallest rank, if any. A **randomized online algorithm** is a probability distribution over deterministic online algorithms.

## Depends on

- [Deterministic online bipartite matching algorithm](../online-bipartite-matching/online-matcher.md)

## Sources

- R. M. Karp, U. V. Vazirani and V. V. Vazirani, "An Optimal Algorithm for On-line Bipartite Matching", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
