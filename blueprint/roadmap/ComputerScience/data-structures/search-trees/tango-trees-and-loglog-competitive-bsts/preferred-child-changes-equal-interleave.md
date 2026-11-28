# Preferred-child changes are counted by the interleave bound

For every access sequence $X$, the number of preferred-child changes from left to right or from right to left in the reference tree $P$ while serving $X$ equals $\mathrm{IB}_P(X)$; counting also the first setting of each preferred child, the total number of preferred-child changes is at least $\mathrm{IB}_P(X)$ and at most $\mathrm{IB}_P(X) + n$.

## Proof sketch

The preferred child of $v$ switches between left and right exactly when two consecutive accesses within the subtree of $v$ fall in different regions of $v$, which is an alternation counted by $\mathrm{alt}_v(X)$. The remaining changes are the first settings, from no preferred child to left or right, at most one per node.

## Depends on

- [Preferred children and preferred paths](preferred-paths.md)
- [Wilber's interleave (alternation) bound](../wilber-and-funnel-lower-bounds/interleave-bound.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
