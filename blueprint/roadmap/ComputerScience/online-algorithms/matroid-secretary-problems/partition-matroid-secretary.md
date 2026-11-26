# 1/e-competitive secretary algorithm on unit-capacity partition matroids

On a unit-capacity partition matroid with nonnegative weights and uniformly random arrival order, running the optimal classical secretary cutoff rule independently within each block outputs an independent set whose expected weight is at least $\frac1e\, w(I)$ for every independent set $I$, in particular at least $\mathrm{OPT}/e$.

## Proof sketch

Within a block the elements arrive in a uniformly random relative order, so the optimal cutoff rule hires the block maximum with probability at least $1/e$ for every block size. Summing over blocks, each element of an optimal independent set (one per block) contributes at least $1/e$ of its weight.

## Depends on

- [Matroid secretary problem](matroid-secretary-problem.md)

## Proof depends on

- [Non-asymptotic 1/e bounds for the secretary problem](../prophet-and-secretary-stopping-rules/secretary-nonasymptotic-bounds.md)

## Sources

- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007.
