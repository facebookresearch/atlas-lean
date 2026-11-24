# Transition matrix of the uniform pair-merger walk

A partition of a finite set $s$ is a set of non-empty, pairwise disjoint subsets of $s$ (its blocks) whose union is $s$. The uniform pair-merger walk on the partitions of $s$ has the real transition matrix $T$, indexed by pairs of partitions of $s$, given as follows. If $P$ has $k \ge 2$ blocks, then $T(P, Q) = 1/\binom{k}{2}$ when $Q$ is obtained from $P$ by merging two blocks ($P$ refines $Q$ and $Q$ has $k - 1$ blocks), and $T(P, Q) = 0$ otherwise. If $P$ has fewer than $2$ blocks, then $T(P, P) = 1$ and $T(P, Q) = 0$ for $Q \ne P$.

So one step merges a uniformly chosen unordered pair of distinct blocks, and the partitions with at most one block are absorbing.
