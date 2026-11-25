# The mutation realization solves the mutation martingale problem

Let $\theta_1, \theta_2 \ge 0$, let $P^\theta_x$ be the [canonical path measure of the Wright–Fisher diffusion with mutation](../construction-of-the-neutral-wright-fisher-diffus/mutation-wf-transition-kernel-and-canonical-path.md) started at $x \in [0, 1]$, and let $X$ be its [continuous modification](../construction-of-the-neutral-wright-fisher-diffus/fourth-moment-increment-bound-and-continuous-mod.md), which is [Markov for the kernels $K^\theta_t$](../strong-markov-property-of-the-wright-fisher-diff-2/markov-property-of-the-continuous-canonical-proc.md). Then $X$ solves the [two-way mutation Wright–Fisher martingale problem](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md) without selection: for every $f \in C^2[0, 1]$,

$$f(X_t) - f(X_0) - \int_0^t L_{0,\theta} f(X_s)\, ds, \qquad L_{0,\theta} f(x) = \tfrac12 x(1-x) f''(x) + \tfrac12\bigl(\theta_1(1-x) - \theta_2 x\bigr) f'(x),$$

is a martingale. For polynomials $p$ this follows from $\frac{d}{dt} P^\theta_t p = P^\theta_t L_{0,\theta} p$ and the Markov property; for general $f \in C^2[0, 1]$, approximate $f$, $f'$ and $f''$ uniformly by a polynomial and its derivatives.

## Depends on

- [Fourth-moment increment bound and continuous modification for the mutation diffusion](../construction-of-the-neutral-wright-fisher-diffus/fourth-moment-increment-bound-and-continuous-mod.md)
- [Markov property of the continuous canonical process of a Chapman-Kolmogorov family](../strong-markov-property-of-the-wright-fisher-diff-2/markov-property-of-the-continuous-canonical-proc.md)
- [Two-way mutation (and selection) Wright-Fisher martingale problem](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)
- [Mutation Wright–Fisher transition kernel and canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/mutation-wf-transition-kernel-and-canonical-path.md)

## Proof depends on

- [Mutation WF Feller semigroup via polynomial duality and chain limits](../wright-fisher-semigroup-and-moment-duality/mutation-wf-feller-semigroup-via-polynomial-dual.md)
- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

A full proof page must still establish the polynomial case from the semigroup identity and the Markov property, and the $C^2$ extension by simultaneous polynomial approximation of $f$, $f'$ and $f''$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, <https://doi.org/10.1002/9780470316658>
