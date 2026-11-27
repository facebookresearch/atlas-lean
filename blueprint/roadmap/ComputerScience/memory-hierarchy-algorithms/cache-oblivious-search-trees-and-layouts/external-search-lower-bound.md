# Comparison-based search needs $\Omega(\log_B N)$ I/Os

In the external-memory model with blocks of $B$ records, every comparison-based algorithm that starts from an empty cache, holding no information about the stored keys, and locates a query key among $N$ stored keys (finding its predecessor) uses at least $\log_{B+1}(N+1)$, hence $\Omega(\log_{B+1} N)$, block reads in the worst case. The cold start is needed: a cache preloaded with $N-1$ of the keys leaves at most one block read to do.

## Proof sketch

Since the cache starts empty, before any I/O all $N + 1$ predecessor answers are possible. Reading a block of $B$ keys and comparing the query with them partitions the remaining candidates into at most $B + 1$ intervals, so each I/O reduces the number of possible answers by a factor of at most $B+1$, and $\log_{B+1}(N+1)$ reads are necessary.

## Depends on

- [The external-memory model](../external-memory-algorithms/the-external-memory-model.md)

## Sources

- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
- Erik D. Demaine, "Cache-Oblivious Algorithms and Data Structures", Lecture Notes from the EEF Summer School on Massive Data Sets (2002), Theorem 7.
