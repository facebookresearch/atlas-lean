# The neutral K-allele Wright–Fisher semigroup on the simplex by multinomial duality

Let $K \ge 2$ and $\Delta$ the simplex of allele frequencies, with neutral evolution and either no mutation or parent-independent mutation scaled with the population size: in one generation on $M \ge \theta/2$ gene copies, each copy's parental type is kept with probability $1 - \theta/(2M)$ and redrawn from a fixed probability vector $\nu$ with probability $\theta/(2M)$, and the next generation is a multinomial sample of size $M$ from the resulting type frequencies. The powers $\lfloor tM \rfloor$ of this one-generation operator map the polynomials of degree at most $n$ into themselves, triangularly in the degree, and converge on them. By [the extension of limits of uniform contractions from a dense set](tendsto-apply-of-dense.md) they converge on all of $C(\Delta)$ to a Feller semigroup whose generator acts on polynomials as [the $K$-allele generator](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md).

## Depends on

- [Limits of uniform contractions extend from a dense set](tendsto-apply-of-dense.md)
- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [Multinomial distribution](../../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)

## Proof depends on

- [Neutral Wright–Fisher diffusion semigroup](wf-semigroup.md)

## Expansion

1. Invariance and triangularity of the polynomials of degree at most $n$ under one multinomial generation, and the limit on them.
2. Extension to $C(\Delta)$ by contraction and density.
3. Projection consistency: the coordinate $x_i$ evolves as the two-allele diffusion, neutral without mutation and with the induced two-type mutation rates under parent-independent mutation, as for [the neutral two-allele semigroup](wf-semigroup.md).

## Sources

- S. N. Ethier, A class of degenerate diffusion processes occurring in population genetics, *Comm. Pure Appl. Math.* 29 (1976), 483–493, <https://doi.org/10.1002/cpa.3160290503> (degenerate diffusions).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10, Section 2.
