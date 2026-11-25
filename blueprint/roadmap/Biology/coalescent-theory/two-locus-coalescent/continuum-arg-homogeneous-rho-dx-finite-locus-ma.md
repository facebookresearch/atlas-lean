# Continuum ARG with homogeneous recombination: finite-locus marginals and two-point law

Consider the [marked whole-chromosome ancestral recombination graph](../pairwise-differences-under-poisson-mutation/marked-whole-chromosome-arg-on-0-1-with-homogene.md) on $[0, 1)$ with recombination intensity $\rho\, dx$, $\rho \ge 0$. For loci $0 \le x_1 < \cdots < x_k < 1$, project the graph to these loci and apply the reduction map. The result has the law of the reduced [coalescent with recombination on $k$ loci](coalescent-with-recombination-ancestral-material.md) with breakpoint rates

$$\rho_i = \rho\, (x_{i+1} - x_i), \qquad 1 \le i < k.$$

The cut is half-open, and the intensity has no atoms, so no breakpoint is counted twice.

In particular, for $n = 2$ the pair $(T_x, T_y)$ of coalescence times at two loci has the two-locus law with recombination rate $\rho\, \lvert x - y \rvert$, so $\operatorname{Cov}(T_x, T_y) = f(\rho \lvert x - y \rvert)$ with $f(r) = (r + 18)/(r^2 + 13 r + 18)$, as in [the covariance of the coalescence times](covariance-coalescence-times.md).

General recombination measures are a separate target: [the continuum ARG with a general recombination measure](continuum-arg-with-a-general-finite-recombinatio.md).

## Depends on

- [Marked whole-chromosome ARG on [0,1) with homogeneous recombination: construction](../pairwise-differences-under-poisson-mutation/marked-whole-chromosome-arg-on-0-1-with-homogene.md)
- [Coalescent with recombination: ancestral-material state space and generator](coalescent-with-recombination-ancestral-material.md)
- [Covariance of the coalescence times, path form](covariance-coalescence-times.md)

## Proof depends on

- [Finitely many breakpoints and a jointly measurable local-tree field](../pairwise-differences-under-poisson-mutation/finitely-many-breakpoints-and-a-jointly-measurab.md)

## Expansion

1. The projection and reduction maps, and the equality of the generators of the projected process and of the finite-locus process.
2. Checks: with three loci, the rate at which $x_1$ is separated from $x_3$ is $\rho(x_3 - x_1)$, the sum of the rates of the two gaps. The two-point covariance is $f(\rho \lvert x - y \rvert)$.

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (the ancestral recombination graph).
- C. Wiuf and J. Hein, Recombination as a point process along sequences, *Theor. Popul. Biol.* 55 (1999), 248–259, <https://pubmed.ncbi.nlm.nih.gov/10366550/> (local trees along the sequence).
