# The Feller semigroup of the Wright–Fisher diffusion with mutation

Let $\theta_1, \theta_2 \ge 0$ and $\theta = \theta_1 + \theta_2$, with no selection. Then:

1. $\mathcal{L}_{0, \theta}$ maps the polynomials of degree at most $n$ into themselves, for every $n$;
2. the rescaled powers of the Bernstein-type operator of one Wright–Fisher generation with mutation converge on polynomials and, by [the extension of limits of uniform contractions from a dense set](tendsto-apply-of-dense.md), on all of $C[0, 1]$, to a positive, unital, strongly continuous contraction semigroup $P^{\theta}_t$;
3. the generator of $P^{\theta}_t$ acts on polynomials as $\mathcal{L}_{0, \theta}$.

## Depends on

- [Limits of uniform contractions extend from a dense set](tendsto-apply-of-dense.md)

## Proof depends on

- [Martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)
- [Uniform generator convergence of the Wright–Fisher chain with selection and mutation](../wright-fisher-diffusion-with-mutation/uniform-generator-convergence-with-selection-and.md)
- [One generation of the neutral Wright–Fisher chain](wf-step.md)

## Expansion

1. Triangularity of $\mathcal{L}_{0, \theta}$ on polynomials, and convergence on polynomials from [the uniform generator convergence](../wright-fisher-diffusion-with-mutation/uniform-generator-convergence-with-selection-and.md).
2. Extension to $C[0, 1]$ by contraction and density.
3. Checks: $\theta = 0$ recovers the neutral Wright–Fisher semigroup, and for $\theta > 0$, $P^{\theta}_t x = \theta_1/\theta + (x - \theta_1/\theta)\, e^{-\theta t/2}$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10, Sections 1 and 2.
- S. N. Ethier, A class of degenerate diffusion processes occurring in population genetics, *Comm. Pure Appl. Math.* 29 (1976), 483–493, <https://doi.org/10.1002/cpa.3160290503> (degenerate diffusions in population genetics).
