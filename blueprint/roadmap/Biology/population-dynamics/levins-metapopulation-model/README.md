# Levins metapopulation model

The Levins patch-occupancy model follows the fraction `p` of occupied habitat patches under
colonization at rate `c` and local extinction at rate `e`, `p' = c p (1 - p) - e p`. The second part
adds immigration from a mainland at rate `m` per empty patch, `p' = c p (1 - p) - e p + m (1 - p)`.
Each page states the sign conditions on `c`, `e`, `m` and on the initial value that its result
needs.

## The Levins equation and its equilibria

- [Colonization–extinction balance of the Levins model](balance-2.md)
- [Solution of the Levins equation](is-solution-2.md)
- [Persistence equilibrium of the Levins model](persistence-eq.md)
- [For c ≠ 0, the balance factors as c p (p* − p)](balance-eq-mul-2.md)
- [For c ≠ 0, the balance vanishes exactly at 0 and p*](balance-eq-zero-iff-2.md)
- [The constant function 0 solves the Levins equation](is-solution-const-zero.md)
- [For c ≠ 0, the constant function p* solves the Levins equation](is-solution-const-persistence-eq.md)
- [A Levins solution gives an SIS solution with S = 1 − p and N = 1](to-sis.md)

## Persistence threshold of the Levins model

- [For c > 0, the persistence equilibrium is positive iff e < c](persistence-eq-pos-iff.md)
- [For c > 0 and e ≥ 0, the persistence equilibrium is at most 1](persistence-eq-le-one.md)
- [For c > 0 and e > 0, the persistence equilibrium is less than 1](persistence-eq-lt-one.md)
- [For c > 0 and e ≥ 0, 0 < p* ≤ 1 exactly when e < c](persistence-eq-mem-ioc-iff.md)

## Linearization of the Levins model at its equilibria

- [The derivative of the balance in p is c − e − 2cp](has-deriv-at-balance-2.md)
- [The linearization at extinction has slope c − e](has-deriv-at-balance-zero.md)
- [For c ≠ 0, the linearization at p* has slope e − c](has-deriv-at-balance-persistence-eq.md)

## Explicit solution, existence and uniqueness without immigration

- [Explicit solution of the Levins equation](levins.md)
- [For c, p₀ ≥ 0, the explicit solution solves the Levins equation](is-solution-levins.md)
- [For c, e ≥ 0, the explicit solution stays in the closed unit interval](levins-mem-icc.md)
- [For c ≥ 0 and p₀ > 0, the explicit solution is positive for t ≥ 0](levins-pos.md)
- [For c > 0 and e < c, the explicit solution is a logistic curve](levins-eq-logistic.md)
- [Global existence of a solution staying in the closed unit interval](exists-is-solution-2.md)
- [Two solutions with the same initial value agree for t ≥ 0](eq-of-initial.md)
- [For c ≥ 0, a solution with p(0) ≥ 0 equals the explicit one for t ≥ 0](eq-levins.md)
- [For c, e ≥ 0, solutions stay in the closed unit interval](mem-icc-2.md)
- [For c ≥ 0, a solution with p(0) > 0 stays positive](pos-2.md)

## Stability notions for the Levins model

- [Lyapunov stability for the Levins equation](is-lyapunov-stable-2.md)
- [Global attraction for the Levins equation](is-globally-attracting-2.md)
- [Global stability for the Levins equation](is-globally-stable-3.md)

## Extinction when colonization does not beat extinction

- [For 0 ≤ c ≤ e, a solution with p(0) ≥ 0 never exceeds p(0)](le-initial.md)
- [For 0 ≤ c ≤ e and e > 0, every solution with p(0) ≥ 0 tends to 0](tendsto-zero.md)
- [For 0 ≤ c ≤ e and e > 0, extinction is globally stable](extinction-is-globally-stable.md)
- [For c, e > 0, extinction is globally attracting iff c ≤ e](tendsto-zero-iff-le.md)

## Persistence when colonization beats extinction

- [For c > 0 and e < c, closed form of the gap p(t) − p*](levins-sub-persistence-eq.md)
- [For c > 0, e < c and p₀ > 0, p(t) is never farther from p* than p₀](abs-levins-sub-le.md)
- [For c > 0, e < c and p₀ > 0, the distance to p* decays exponentially](abs-levins-sub-le-exp.md)
- [For 0 ≤ e < c, every solution with p(0) > 0 tends to p*](tendsto-persistence-eq.md)
- [For 0 ≤ e < c, the persistence equilibrium is globally stable](persistence-is-globally-stable.md)
- [For 0 ≤ e < c, extinction is not Lyapunov stable](not-is-lyapunov-stable-zero.md)

## The model with immigration

- [Colonization–extinction–immigration balance](balance.md)
- [Forward solution of the Levins equation with immigration](is-solution.md)
- [Without immigration the balance is the Levins balance](balance-zero-right.md)
- [Without immigration the solutions are the Levins solutions](is-solution-zero-right-iff.md)
- [With nonzero immigration, extinction is not an equilibrium](balance-zero.md)
- [The balance at full occupancy is minus the extinction rate](balance-one.md)
- [Derivative of the balance with immigration](has-deriv-at-balance.md)

## The immigration equilibrium

- [Discriminant of the equilibrium quadratic](disc.md)
- [Immigration equilibrium](immigration-eq.md)
- [For m > 0 and e ≥ 0, the equilibrium denominator is positive](denom-pos.md)
- [The immigration equilibrium is a zero of the balance](balance-immigration-eq.md)
- [For m > 0, the immigration equilibrium is positive and at most 1](immigration-eq-mem-ioc.md)
- [With local extinction, the immigration equilibrium is below 1](immigration-eq-lt-one.md)
- [For c > 0 and m > 0, the equilibrium is the quadratic-formula root](immigration-eq-eq-quadratic.md)
- [For m > 0, the immigration equilibrium is the only nonnegative zero](balance-eq-zero-iff.md)
- [For m > 0, there is exactly one nonnegative equilibrium](exists-unique-equilibrium.md)
- [For c > 0, as m ↓ 0, p̂ tends to the larger Levins equilibrium](tendsto-immigration-eq-zero.md)

## Factorization and linearization at the immigration equilibrium

- [At a positive equilibrium q, m / q equals c q - c + e + m](div-eq-of-balance-eq-zero.md)
- [Factorization of the balance through any positive equilibrium](balance-eq-mul-of-eq.md)
- [For m > 0, the balance factors through the immigration equilibrium](balance-eq-mul.md)
- [For m > 0, the extinction rate in terms of the equilibrium p̂](one-sub-immigration-eq-mul.md)
- [Return rate at the immigration equilibrium](rate.md)
- [For m > 0, the slope of the balance at p̂ is minus the return rate](has-deriv-at-balance-immigration-eq.md)

## Explicit solution with immigration

- [Closed-form trajectory of the shifted Riccati equation](riccati-traj.md)
- [Explicit solution of the Levins equation with immigration](solution.md)
- [From p₀ ≥ 0, the explicit solution solves the equation for t ≥ 0](is-solution-solution.md)
- [For p₀ ≥ 0, a solution with immigration exists for all t ≥ 0](exists-is-solution.md)

## Invariance and bounds with immigration

- [For m > 0, a solution that starts nonnegative stays nonnegative](nonneg.md)
- [For m > 0, occupancy is positive at every positive time](pos.md)
- [Exponential upper bound on the excess over a positive equilibrium](sub-le-mul-exp-of-eq.md)
- [For m > 0, exponential upper bound on the excess over p̂](sub-le-mul-exp.md)
- [For m > 0, a solution never exceeds the larger of its start and p̂](le-max.md)
- [For m > 0, the unit interval is forward invariant](mem-icc.md)

## Stability with immigration

- [Lyapunov stability for the model with immigration](is-lyapunov-stable.md)
- [Global attraction for the model with immigration](is-globally-attracting.md)
- [Global stability for the model with immigration](is-globally-stable.md)
- [For m > 0, exponential decay of the distance to a positive equilibrium](abs-sub-le-exp-of-eq.md)
- [For m > 0, exponential decay of the distance to p̂](abs-sub-le-exp.md)
- [For m > 0, every solution starting nonnegative tends to p̂](tendsto-immigration-eq.md)
- [For m > 0, the immigration equilibrium is globally stable](is-globally-stable-2.md)
- [For 0 ≤ c ≤ e with e > 0, propagule rain ensures persistence](propagule-rain-persistence.md)
