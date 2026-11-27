# Continuum ARG with a general finite recombination measure

This page covers a research programme: extending [the construction with homogeneous recombination](../pairwise-differences-under-poisson-mutation/marked-whole-chromosome-arg-on-0-1-with-homogene.md), [its breakpoint finiteness](../pairwise-differences-under-poisson-mutation/finitely-many-breakpoints-and-a-jointly-measurab.md) and [its finite-locus marginals](continuum-arg-homogeneous-rho-dx-finite-locus-ma.md) from the intensity $\rho\, dx$ to an arbitrary finite measure $\rho(dx)$ on $[0, 1)$, possibly with atoms.

The breakpoint of a recombination has law $\rho / \rho([0, 1))$, with the cut convention that a breakpoint $b$ sends $[0, b)$ to one part and $[b, 1)$ to the other. Loci $x < y$ are then separated exactly when $x < b \le y$, so the finite-locus marginals have breakpoint rates $\rho_i = \rho((x_i, x_{i+1}])$.

## Expansion

Split the programme into separately stated results, each with hypotheses fixed from a source, with the half-open cut convention fixed. They should establish:

1. With an atom at $b = 1/2$ and loci $1/2$ and $3/4$, the separation rate is $\rho((1/2, 3/4]) = 0$: both loci lie to the right of the cut.
2. With an atom of mass $1$ at $1/2$ and loci $1/4$ and $1/2$, the separation rate is $1$.
3. The rates of adjacent gaps $(x, y]$ and $(y, z]$ add up to that of $(x, z]$, with no double counting.

Prerequisites:

- [Continuum ARG with homogeneous recombination: finite-locus marginals and two-point law](continuum-arg-homogeneous-rho-dx-finite-locus-ma.md)

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (the ancestral recombination graph).
