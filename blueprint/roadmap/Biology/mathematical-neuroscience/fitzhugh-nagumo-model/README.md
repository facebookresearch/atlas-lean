# FitzHugh–Nagumo model

## The model

- [Voltage component of the FitzHugh–Nagumo field](v-field.md)
- [Recovery component of the FitzHugh–Nagumo field](w-field.md)
- [The FitzHugh–Nagumo vector field](field.md)
- [Solution of the FitzHugh–Nagumo system](is-solution.md)

## Energy, the trapping ellipse, and forward invariance

- [Energy whose sublevel sets are the trapping ellipses](energy.md)
- [Energy flux of the FitzHugh–Nagumo field](energy-flux.md)
- [For ε ≠ 0, closed form of the energy flux](energy-flux-eq.md)
- [Constant term of the dissipation inequality](absorb-const.md)
- [Decay rate of the dissipation inequality](decay-rate.md)
- [Trapping radius of the FitzHugh–Nagumo energy](trap-radius.md)
- [For b, ε > 0, the energy flux obeys a dissipation inequality](energy-flux-le.md)
- [For b, ε > 0, the field points strictly inward on large ellipses](energy-flux-neg-of-energy-eq.md)
- [Derivative of the energy along a trajectory](has-deriv-at-energy.md)
- [For b, ε > 0, large energy ellipses are forward invariant](energy-le.md)
- [For b, ε > 0, every solution stays in a fixed ellipse](energy-le-max.md)
- [For b, ε > 0, exponential absorption into the trapping ellipses](energy-le-absorb.md)

## Global existence and forward uniqueness

- [The FitzHugh–Nagumo field is locally Lipschitz](field-locally-lipschitz.md)
- [For ε > 0, the energy sublevel sets are compact](is-compact-energy-le.md)
- [For b, ε > 0, solutions exist for all forward time](exists-is-solution.md)
- [Forward uniqueness of FitzHugh–Nagumo solutions](eq-of-initial.md)

## Equilibria

- [Equilibrium of the FitzHugh–Nagumo field](is-equilibrium.md)
- [Equilibrium cubic of the FitzHugh–Nagumo model](eq-cubic.md)
- [For b, ε ≠ 0, equilibria are the roots of the equilibrium cubic](is-equilibrium-iff.md)
- [For 0 < b ≤ 1, the equilibrium cubic is strictly decreasing](eq-cubic-strict-anti.md)
- [For 0 < b ≤ 1, the equilibrium cubic has a root](exists-eq-cubic-eq-zero.md)
- [For 0 < b ≤ 1 and ε ≠ 0, there is exactly one rest state](exists-unique-equilibrium.md)

## Linearization

- [Jacobian matrix of the FitzHugh–Nagumo field](jacobian.md)
- [The Jacobian entries are the partial derivatives of the field](jacobian-eq-partials.md)
- [Trace of the FitzHugh–Nagumo Jacobian](jac-trace.md)
- [Determinant of the FitzHugh–Nagumo Jacobian](jac-det.md)
- [Characteristic polynomial of the FitzHugh–Nagumo Jacobian](det-jacobian-sub.md)

## Classification of the FitzHugh–Nagumo equilibria

- [Linearization type of a FitzHugh–Nagumo equilibrium](equilibrium-type.md)
- [For ε > 0, the type is a saddle iff b − b v² > 1](equilibrium-type-eq-saddle-iff.md)
- [For 0 < b < 1 and ε > 0, the Jacobian determinant is positive](jac-det-pos.md)
- [For 0 < b < 1, ε > 0, linear instability iff v² < 1 − ε b](is-linearly-unstable-iff-of-lt-one.md)
- [The Jacobian is Hurwitz iff z² − τ z + Δ has only stable roots](is-hurwitz-jacobian-iff-is-linearly-stab.md)
- [For 0 < b < 1, ε > 0, linear stability iff v² > 1 − ε b](is-hurwitz-jacobian-iff-of-lt-one.md)
- [For 0 < b < 1, ε > 0, the type is a linear center iff v² = 1 − ε b](equilibrium-type-eq-center-iff-of-lt-one.md)
- [For 0 < b < 1, ε > 0, v² = 1 − ε b gives purely imaginary eigenvalues](re-eq-zero-and-im-ne-zero-of-mem-spectru.md)

## Post-pulse drift of a single pulse

- [Voltage rising after a pulse](is-rising-after-pulse.md)
- [Voltage falling after a pulse](is-falling-after-pulse.md)
- [Voltage field after a pulse from the voltage nullcline](v-field-pulse.md)
- [Lower quadratic-formula expression of the post-pulse factor](pulse-root-low.md)
- [Upper quadratic-formula expression of the post-pulse factor](pulse-root-high.md)
- [For v² < 4, the two pulse roots are distinct](pulse-root-low-lt-pulse-root-high.md)
- [On the voltage nullcline with v² ≤ 4, rising pulses form a window](is-rising-after-pulse-iff.md)
- [On the voltage nullcline with v² ≤ 4, falling pulses avoid the window](is-falling-after-pulse-iff.md)
- [For v < −1, the lower pulse root is positive](pulse-root-low-pos.md)
- [For v ≤ −1, the lower pulse root is nonnegative](pulse-root-low-nonneg.md)
- [For v > −1, the lower pulse root is negative](pulse-root-low-neg.md)
- [Small pulses from the left nullcline branch make the voltage fall](is-falling-after-pulse-of-lt-pulse-root.md)
- [Linearly stable rest states with −2 ≤ v < −1 and post-pulse drift](stable-rest-pulse-drift.md)
- [Linearly stable rest states with −2 < v < −1 have a rising window](stable-rest-rising-pulse-window.md)

## Single-pulse response of the full system

- [Bound on the drift of the recovery variable](abs-w-sub-le.md)
- [Bound on v + a − b w over an energy ellipse](abs-le-of-energy-le.md)
- [Upper barrier for the voltage while the recovery stays close](v-le-of-barrier.md)
- [Lower barrier for the voltage while the recovery stays close](le-v-of-barrier.md)
- [Reaching a voltage level within an explicit time](exists-v-ge.md)
- [Response of the full system to a single pulse from rest](single-pulse-response.md)

## Return to rest

- [Energy centred at a rest state](rest-energy.md)
- [Post-pulse factor at a rest voltage](rest-factor.md)
- [Flux of the field through the centred energy levels](rest-flux.md)
- [The post-pulse factor is at most 1 − vr²/4](rest-factor-le.md)
- [Bound on the post-pulse factor for displacements up to ρ](rest-factor-le-of-abs-le.md)
- [For vr² ≤ 4, the post-pulse factor is positive exactly on the window](rest-factor-pos-iff.md)
- [Voltage field in coordinates centred at an equilibrium](v-field-eq-rest-factor.md)
- [Recovery field in coordinates centred at an equilibrium](w-field-eq-shift.md)
- [For ε ≠ 0, closed form of the centred flux at an equilibrium](rest-flux-eq.md)
- [Derivative of the centred energy along a trajectory](has-deriv-at-rest-energy.md)
- [For ε > 0, a bound on the centred flux from a bound on the factor](rest-flux-le.md)
- [For ε > 0, an exponential bound on the centred energy along solutions](rest-energy-le-exp.md)
- [For ε > 0, a global exponential bound on the centred energy](rest-energy-le-exp-global.md)
- [For b, ε > 0 and vr² > 1, small balls of centred energy are invariant](rest-energy-le-of-basin.md)
- [For b, ε > 0 and vr² > 1, exponential decay to rest from a small ball](rest-energy-le-exp-of-basin.md)
- [An exponential bound on the centred energy gives convergence](tendsto-of-rest-energy-le-exp.md)
- [For b, ε > 0 and vr² > 4, every solution returns to rest](tendsto-rest-of-four-lt-sq.md)
- [For b, ε > 0 and vr² > 1, solutions from a small ball return to rest](tendsto-rest-of-basin.md)

## Periodic orbits

- [For b, ε > 0, periodic orbits with post-pulse factor ≤ 0 are at rest](eq-rest-of-periodic.md)
- [For b, ε > 0 and vr² ≥ 4, periodic solutions are at rest](eq-rest-of-periodic-of-four-le-sq.md)
- [For b, ε > 0 and vr² ≤ 4, nonconstant periodic orbits enter the window](exists-mem-pulse-window-of-periodic.md)
