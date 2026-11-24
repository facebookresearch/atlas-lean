# Fracture, fatigue crack growth and failure margins

## Mode-I stress intensity and the critical crack length

- [Mode-I stress intensity factor $K_I(a) = Y \sigma \sqrt{\pi a}$](mode-istress-intensity.md)
- [Critical crack length $a_c = (K_{IC}/(Y\sigma))^2/\pi$](critical-crack-length.md)
- [Crack failure: the mode-I stress intensity reaches the toughness](crack-failure.md)
- [The mode-I stress intensity vanishes at zero crack length](mode-istress-intensity-zero.md)
- [Positive toughness, geometry factor and stress give $a_c > 0$](critical-crack-length-pos.md)
- [For positive $K_{IC}, Y, \sigma$: $K_I(a_c) = K_{IC}$](mode-istress-intensity-critical-crack-le.md)
- [For $K_{IC}, Y, \sigma > 0$, $a \ge 0$: $K_I < K_{IC}$ iff $a < a_c$](mode-istress-intensity-lt-iff-lt-critica.md)
- [For $K_{IC}, Y, \sigma > 0$, $a \ge 0$: crack failure iff $a_c \le a$](crack-failure-iff-critical-crack-length.md)

## Paris-law crack growth: power branch

- [Paris-law crack growth, power branch: $(a_0^r + rKN)^{1/r}$](paris-crack-pow.md)
- [Paris life in the power branch, $N_f = (a_c^r - a_0^r)/(rK)$](paris-life-pow.md)
- [For $r \ne 0$ and $a_0 > 0$, the power-branch crack starts at $a_0$](paris-crack-pow-zero.md)
- [For $r \ne 0$ and positive base, the power crack solves the Paris law](has-deriv-at-paris-crack-pow.md)
- [For a nonnegative base, $a(N)^r = a_0^r + rKN$ in the power branch](paris-crack-pow-pow.md)
- [For $K > 0$, $r \ne 0$, $0 < a_0 < a_c$: positive power-branch life](paris-life-pow-pos.md)
- [For $K, a_0, a_c > 0$, $r \ne 0$: power crack reaches $a_c$ at $N_f$](paris-crack-pow-at-life.md)
- [Power branch, $K>0$, $0<a_0<a_c$, base $>0$: $a<a_c$ iff $N<N_f$](paris-crack-pow-lt-iff.md)
- [For $m > 2$, the power-branch Paris life precedes the blow-up count](paris-life-pow-lt-blowup.md)

## Paris-law crack growth: logarithmic branch

- [Paris-law crack growth, logarithmic branch: $a_0 e^{KN}$](paris-crack-exp.md)
- [Paris life in the logarithmic branch, $N_f = \log(a_c/a_0)/K$](paris-life-exp.md)
- [For $K > 0$, $0 < a_0 < a_c$, the logarithmic Paris life is positive](paris-life-exp-pos.md)
- [For $K, a_0, a_c > 0$: the logarithmic crack reaches $a_c$ at its life](paris-crack-exp-at-life.md)
- [For $K > 0$, $0 < a_0 < a_c$: $a_0 e^{KN} < a_c$ iff $N < N_f$](paris-crack-exp-lt-iff.md)

## Demand, allowable and margin of safety

- [Dimensional margin of a demand against an allowable](dimensional-margin.md)
- [Failure event: the demand reaches the allowable](demand-failure.md)
- [Margin of safety for a positive demand](margin-of-safety.md)
- [Failure is a nonpositive dimensional margin](demand-failure-iff-dimensional-margin-no.md)
- [A demand equal to the allowable fails, with zero margin](demand-failure-self.md)
- [For a positive demand the margin is demand times margin of safety](dimensional-margin-eq-mul-margin-of-safe.md)
- [For a positive demand the margin of safety has the sign of the margin](sign-margin-of-safety.md)
- [For a positive demand, failure is a nonpositive margin of safety](demand-failure-iff-margin-of-safety-nonp.md)
- [Changing the stress unit by a positive factor](margin-unit-change.md)
- [Zero demand against a positive allowable: margin $A$, no failure](dimensional-margin-zero-demand.md)
- [For a positive allowable, the ratio at zero demand misreports failure](ratio-at-zero-demand-misreports.md)
- [Crack failure as a demand event ($K_I$ against $K_{IC}$)](crack-failure-iff-demand-failure.md)

## Axial bar with a calibrated yield functional

- [Yield functional calibrated by the tensile test](uniaxial-calibrated.md)
- [Axial stress of the uniform-load displacement of a bar](axial-stress.md)
- [For $EA, A_{cs} > 0$ the axial stress is $q (L - 2x) / (2 A_{cs})$](axial-stress-eq.md)
- [Demand of the axial stress through a calibrated yield functional](axial-demand-eq.md)
- [The bar fails at some section exactly when the end demand reaches $A$](axial-bar-failure-iff.md)

## Lifetimes as damage hitting times

- [Lifetime as the hitting time of the damage threshold](damage-lifetime.md)
- [The hit condition is the demand event at the threshold](mem-damage-hit-set-iff.md)
- [For a continuous damage path the hit set is closed](is-closed-damage-hit-set.md)
- [For a nondecreasing damage path the hit set is upward closed](is-upper-set-damage-hit-set.md)
- [For continuous nondecreasing damage, up at $t$ iff below threshold](lt-damage-lifetime-iff.md)
- [For continuous nondecreasing damage, failure by $t$ is failure at $t$](damage-lifetime-le-iff.md)
- [The lifetime is infinite iff the damage never reaches the threshold](damage-lifetime-eq-top-iff.md)
- [A component failed at time zero has lifetime zero](damage-lifetime-eq-zero.md)

## Measurable lifetimes and monotone systems

- [Lifetime of measurable continuous monotone damage is measurable](measurable-damage-lifetime.md)
- [Continuous nondecreasing damage: monotone system up iff $x(t) \in A$](lt-system-lifetime-damage-iff.md)
- [System lifetime of measurable continuous monotone damage is measurable](measurable-system-lifetime-damage.md)

## The saturated crack event path

- [Saturated crack event path under a constant load frequency](saturated-crack-path.md)
- [For $f > 0$, the event path equals $a(N_f)$ from time $N_f / f$ on](saturated-crack-path-of-le.md)

## The Paris lifetime: power branch

- [Along the event path the power-branch base stays positive](saturated-crack-path-pow-base-pos.md)
- [The power-branch event path is continuous and nondecreasing](continuous-monotone-saturated-crack-path.md)
- [Up to failure the event path $a(f t)$ solves $da/dt = f K a^{1-r}$](has-deriv-at-paris-crack-pow-time.md)
- [For $f > 0$, the power-branch lifetime is $N_f / f$](damage-lifetime-saturated-crack-path-pow.md)
- [At $f = 0$ a crack below $a_c$ never fails, power branch](damage-lifetime-saturated-crack-path-pow-2.md)
- [For $r < 0$, the failure time comes strictly before the blow-up time](failure-time-lt-blowup-time.md)

## The Paris lifetime: logarithmic branch and initial failure

- [The logarithmic-branch event path is continuous and nondecreasing](continuous-monotone-saturated-crack-path-2.md)
- [Up to failure the event path $a(f t)$ solves $da/dt = f K a$](has-deriv-at-paris-crack-exp-time.md)
- [For $f > 0$, the logarithmic-branch lifetime is $N_f / f$](damage-lifetime-saturated-crack-path-exp.md)
- [At $f = 0$ a crack below $a_c$ never fails, logarithmic branch](damage-lifetime-saturated-crack-path-exp-2.md)
- [A crack starting at or above the critical length has lifetime zero](damage-lifetime-initially-failed.md)

## A solid circular shaft under bending and torsion

- [Second moment of area of a solid circular section](circle-second-moment.md)
- [Polar second moment of area of a solid circular section](circle-polar-moment.md)
- [Outer-fiber bending stress of a solid circular shaft](shaft-bending-stress.md)
- [Surface torsional shear stress of a solid circular shaft](shaft-shear-stress.md)
- [For $d \ne 0$, $\sigma = 32M/(\pi d^3)$ and $\tau = 16T/(\pi d^3)$](shaft-stresses-eq.md)
- [Stress state at the critical point of a shaft in bending and torsion](bending-torsion-state.md)
- [Functional calibrated on bending–torsion states with a shear factor](bending-torsion-calibrated.md)
- [A bending–torsion calibration is a tensile-test calibration](uniaxial-calibrated-2.md)
- [Demand at the critical point of a solid circular shaft](shaft-demand-eq.md)
- [Minimum diameter of a solid circular shaft for an allowable stress](shaft-min-diameter.md)
- [A shaft with $d > 0$ meets the allowable exactly when $d \ge d_{\min}$](shaft-demand-le-iff.md)
- [A shaft with $d > 0$ does not fail exactly when $d > d_{\min}$](not-demand-failure-iff.md)
- [For a nonzero load the minimum shaft diameter is positive](shaft-min-diameter-pos.md)

## Shaft sizing: boundary examples

- [At zero diameter the stress formulas give zero demand and no failure](zero-diameter-misreports.md)
- [With $M \ne 0$, a stress concentration $K > 1$ overloads $d_{\min}$](stress-concentration-exceeds-at-min-diam.md)
