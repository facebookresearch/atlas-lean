# Ergodic theorem for complex-balanced reaction networks

The stochastic mass-action chain of a chemical reaction network moves on the molecule counts `ℕ^S`.
When `c` is complex balanced for the rate constants, the product-form Poisson weights `π_c` solve
its stationary master equation, and for `c ≥ 0` they sum to `1` over `ℕ^S` (Anderson, Craciun &
Kurtz 2010). For a jointly measurable regenerative process on a probability space whose cycles have
finite mean length, the renewal–reward theorem gives almost sure limits of the time averages of
bounded measurable observables; when the singletons of the state space are measurable, a stationary
law that charges the regeneration state forces cycles of finite mean length and identifies the limit
as the mean under that law. Together: for nonnegative rate constants and a complex-balanced `c > 0`,
a jointly measurable process on `ℕ^S`, defined on a probability space, that does not explode, has
law `π_c` at every time `t ≥ 0` and regenerates at a state is positive recurrent, and for each
bounded observable its time averages converge almost surely to the observable's mean under `π_c`.

## The master equation and the product-form weights

- [Unique predecessor along a reaction among states containing its source](fire-eq-iff.md)
- [Stationary chemical master equation](is-stationary-master-solution.md)
- [For nonnegative means, the Poisson weights sum to one over all states](has-sum-poisson-weight.md)

## Deterministic renewal lemmas

- [Deterministic renewal–reward limit for a Lipschitz function](tendsto-div-of-renewal.md)
- [Deterministic renewal limit zero for superlinear renewal times](tendsto-div-zero-of-renewal.md)

## Regenerative processes: occupation times and the strong law

- [Length of a regeneration cycle](cycle-length.md)
- [Occupation integral of an observable along a path](occupation.md)
- [Reward collected during a regeneration cycle](cycle-reward.md)
- [Regeneration of a process at a state](is-regenerative.md)
- [Positive recurrence: integrable first cycle length](is-positive-recurrent.md)
- [Renewal–reward theorem for cycles of finite mean length](ae-tendsto-occupation-div.md)
- [Strong law of large numbers for nonnegative variables of infinite mean](ae-tendsto-avg-at-top-of-not-integrable.md)

## Stationarity: positive recurrence and the value of the limit

- [Mean occupation integral under a stationary law](integral-occupation.md)
- [Under a stationary law, the renewal–reward limit is the space average](integral-div-eq-of-stationary.md)
- [Positive recurrence if a stationary law charges the regeneration state](is-positive-recurrent-of-stationary.md)
- [Ergodic theorem under a stationary law charging the regeneration state](ergodic.md)
- [Ergodic limits transfer to a process with the same cycle laws](ergodic-of-ident-distrib.md)

## The ergodic theorem for complex-balanced stochastic reaction networks

- [Measure on molecule counts with a given mass function](count-law.md)
- [Integral of a bounded function against a probability mass function](integral-count-law.md)
- [Non-explosion of a process on molecule counts](no-explosion.md)
- [Ergodic theorem for complex-balanced networks under regeneration](ergodic-of-is-complex-balanced.md)
- [Product-form limits for a process with the stationary cycle laws](ergodic-of-is-complex-balanced-of-ident.md)

## Related topics

- [Complex balancing and the deficiency-zero theorem](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/README.md): the deterministic theory of complex balancing: complex-balanced states are equilibria of the mass-action system, and a weakly reversible network of deficiency zero with finitely many species and reactions has a complex-balanced state with positive coordinates for every choice of positive rate constants, so the product-form results apply to it.
