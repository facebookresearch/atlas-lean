# Preferred children and preferred paths

Let $P$ be the perfectly balanced BST on $[n]$ used as a reference tree. At any time, the *preferred child* of an internal node $v$ of $P$ is its left child if the most recent access to a key in the subtree of $v$ was in the left subtree or at $v$, its right child if it was in the right subtree, and undefined if no key in the subtree has been accessed. Following preferred children from any node not itself a preferred child yields the *preferred paths*, which partition the nodes of $P$; each preferred path has length at most $\lceil \log_2(n+1) \rceil$.

## Depends on

- [Wilber's interleave (alternation) bound](../wilber-and-funnel-lower-bounds/interleave-bound.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
