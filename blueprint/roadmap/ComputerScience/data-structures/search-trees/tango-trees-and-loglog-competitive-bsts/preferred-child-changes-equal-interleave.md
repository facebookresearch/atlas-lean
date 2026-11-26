# Preferred-child changes are counted by the interleave bound

For every access sequence $X$, the total number of preferred-child changes in the reference tree $P$ while serving $X$ is at least $\mathrm{IB}_P(X) - n$ and at most $\mathrm{IB}_P(X) + n$.

## Proof sketch

The preferred child of $v$ switches exactly when two consecutive accesses within the subtree of $v$ fall on different sides of $v$, which is an alternation counted by $\mathrm{alt}_v(X)$; the first access within each subtree sets a preferred child without an alternation, contributing at most $n$.

## Depends on

- [Preferred children and preferred paths](preferred-paths.md)
- [Wilber's interleave (alternation) bound](../wilber-and-funnel-lower-bounds/interleave-bound.md)

## Proof depends on

- [Preferred children and preferred paths](preferred-paths.md)
- [Wilber's interleave (alternation) bound](../wilber-and-funnel-lower-bounds/interleave-bound.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
