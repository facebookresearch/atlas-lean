# The semigroup route and the stochastic-calculus route give the same neutral Wright–Fisher diffusion

Consider the neutral Wright–Fisher diffusion without mutation or selection. Every weak solution of the stochastic differential equation

$$dX_t = \sqrt{X_t (1 - X_t)}\, dW_t, \qquad X_0 = x \in [0, 1],$$

has the law of the [continuous realization constructed from the transition semigroup](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md) started at $x$. Indeed, a [weak solution of the SDE solves the Wright–Fisher martingale problem](weak-solutions-of-the-wright-fisher-sde-solve-th.md), and the neutral martingale problem is [unique in law](uniqueness-in-law-for-the-neutral-martingale-pro.md). Consequently every law-level statement proved for the semigroup realization, such as the [Kimura–Ohta mean absorption time](../wright-fisher-diffusion/mean-absorption-time.md), holds for every weak solution of the SDE.

## Depends on

- [Weak solutions of the Wright–Fisher SDE solve the Wright–Fisher martingale problem](weak-solutions-of-the-wright-fisher-sde-solve-th.md)
- [Uniqueness in law for the neutral martingale problem (well-posedness)](uniqueness-in-law-for-the-neutral-martingale-pro.md)
- [Continuous modification selected by Kolmogorov's theorem](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md)

## Proof depends on

- [Kimura–Ohta mean absorption time of a neutral allele](../wright-fisher-diffusion/mean-absorption-time.md)

## Expansion

A full proof page must still check that the realization solves the same martingale problem with the same test-function class, and transfer the mean absorption time to weak solutions of the SDE.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapters 5 and 10, <https://doi.org/10.1002/9780470316658>
- A. Etheridge, *Some Mathematical Models from Population Genetics*, École d'Été de Probabilités de Saint-Flour XXXIX-2009, Lecture Notes in Mathematics 2012, Springer, 2011, <https://link.springer.com/book/10.1007/978-3-642-16632-7> (background)
