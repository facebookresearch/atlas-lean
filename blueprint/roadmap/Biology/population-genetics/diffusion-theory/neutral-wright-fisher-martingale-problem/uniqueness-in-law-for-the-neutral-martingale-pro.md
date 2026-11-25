# Uniqueness in law for the neutral Wright–Fisher martingale problem

Let $X$ be a solution of the [martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md) in the neutral case $\sigma = 0$ (that martingale problem has no mutation), with any initial law $\mu$ on $[0, 1]$. Then the law of $X$ on path space is the mixture over $\mu$ of the laws of [the continuous realization of the neutral diffusion](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md) started at each point. In particular the martingale problem is well posed.

The route: [the conditional polynomial-semigroup identity](conditional-polynomial-semigroup-identity-for-ma.md) gives $\mathbb{E}[p(X_t) \mid \mathcal{F}_s] = (P_{t-s} p)(X_s)$ for every polynomial $p$, with $P_t$ the semigroup acting on polynomials through [the generator on polynomials](../wright-fisher-semigroup-and-moment-duality/tendsto-wf-semigroup-sub-div.md). Then [the upgrade from the conditional polynomial identity](conditional-polynomial-identity-implies-markov-p.md) gives the Markov property with semigroup $P_t$ and the uniqueness of the finite-dimensional distributions.

## Depends on

- [Martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
- [Conditional polynomial-semigroup identity for martingale-problem solutions with triangular generators](conditional-polynomial-semigroup-identity-for-ma.md)
- [Conditional polynomial identity implies Markov property and uniqueness in law](conditional-polynomial-identity-implies-markov-p.md)
- [Generator of the Wright–Fisher diffusion on polynomials](../wright-fisher-semigroup-and-moment-duality/tendsto-wf-semigroup-sub-div.md)
- [Continuous modification selected by Kolmogorov's theorem](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md)

## Proof depends on

- [Compactly supported measures are determined by their moments](../../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md)
- [Martingale problems](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

1. The two steps of the route, with the [determination of compactly supported measures by their moments](../../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md) to pass from polynomials to laws on $[0, 1]$.
2. Nonvacuity: the continuous realization satisfies the hypotheses.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Theorem 4.2 (uniqueness from one-dimensional distributions).
- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Springer (1979) (well-posedness).
