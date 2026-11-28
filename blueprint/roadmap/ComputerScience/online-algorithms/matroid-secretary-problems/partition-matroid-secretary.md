# 1/e-competitive secretary algorithm on unit-capacity partition matroids

On a unit-capacity partition matroid with nonnegative well-behaved weights (distinct elements with equal weight have weight $0$) and uniformly random arrival order, running the optimal classical secretary cutoff rule independently within each block outputs an independent set whose expected weight is at least $\frac1e\, w(I)$ for every independent set $I$, in particular at least $\mathrm{OPT}/e$.

## Proof sketch

Within a block the elements arrive in a uniformly random relative order. Well-behaved weights make the block maximum unique whenever it is positive, and equal weights occur only at weight $0$, below every positive weight. So the optimal cutoff rule (reject the first $r - 1$ arrivals, then hire the first one strictly heavier than all earlier ones) hires a positive block maximum with at least its probability in the classical secretary problem with distinct values, which is at least $1/e$ for every block size. Without this hypothesis the rule can hire nothing: in a block of three elements of weight $1$ no arrival is strictly heavier than all earlier ones. Summing over blocks, each element of an optimal independent set (one per block) contributes at least $1/e$ of its weight.

## Depends on

- [Matroid secretary problem](matroid-secretary-problem.md)

## Proof depends on

- [Non-asymptotic 1/e bounds for the secretary problem](../prophet-and-secretary-stopping-rules/secretary-nonasymptotic-bounds.md)

## Sources

- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007, Section 2 (well-behaved inputs) and Section 6 (partition matroids).
