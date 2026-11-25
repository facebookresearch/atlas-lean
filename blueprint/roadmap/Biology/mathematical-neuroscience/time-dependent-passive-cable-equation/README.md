# Time-dependent passive cable equation

## Sealed-end (Neumann) cosine modes

- [Sealed-end cosine mode of a cable](cos-mode.md)
- [Slope of a sealed-end mode at each point](has-deriv-at-cos-mode.md)
- [Derivative function of a sealed-end mode](deriv-cos-mode.md)
- [The slope of a sealed-end mode is differentiable](has-deriv-at-deriv-cos-mode.md)
- [Second derivative of a sealed-end mode](deriv-deriv-cos-mode.md)
- [Every sealed-end mode has zero slope at x = 0](deriv-cos-mode-zero.md)
- [For L ≠ 0, every sealed-end mode has zero slope at x = L](deriv-cos-mode-length.md)
- [The zeroth sealed-end mode is the constant 1](cos-mode-zero-mode.md)
- [Sealed-end modes are bounded by 1 in absolute value](abs-cos-mode-le.md)
- [Sealed-end modes are continuous](continuous-cos-mode.md)
- [For L ≠ 0, orthogonality relations of the sealed-end modes](integral-cos-mode-mul-cos-mode.md)

## Decay rates

- [Decay rate of a sealed-end mode](decay-rate.md)
- [The uniform mode has rate 1/τ](decay-rate-zero.md)
- [For τ > 0, every mode rate is at least 1/τ](one-div-le-decay-rate.md)
- [For τ > 0, every mode rate is positive](decay-rate-pos.md)
- [For τ > 0 and ℓ, L ≠ 0, higher modes decay strictly faster](decay-rate-strict-mono.md)
- [For τ ≠ 0, Rall's ratio of mode rates](decay-rate-div-decay-rate-zero.md)
- [For τ ≠ 0 and ℓ, L > 0, Rall's electrotonic-length formula](div-eq-pi-div-sqrt-decay-rate.md)

## The cable equation and its separated solutions

- [Classical solution of the passive cable equation on a finite cable](is-cable-solution.md)
- [Sealed-end boundary conditions](sealed-ends.md)
- [Finite sealed-end mode expansion](cable-sum.md)
- [Time derivative of the finite expansion](has-deriv-at-cable-sum-time.md)
- [The finite expansion is differentiable in position term by term](has-deriv-at-cable-sum-space.md)
- [Spatial derivative of the finite expansion as a function](deriv-cable-sum-space.md)
- [Second spatial derivative of the finite expansion](has-deriv-at-deriv-cable-sum-space.md)
- [For τ ≠ 0, the finite expansion solves the cable equation](is-cable-solution-cable-sum.md)
- [For L ≠ 0, the finite expansion has sealed ends](sealed-ends-cable-sum.md)
- [Initial profile of the finite expansion](cable-sum-time-zero.md)
- [For τ > 0, the mode rates are nondecreasing in the mode number](decay-rate-mono.md)
- [For τ > 0, uniform bound on the finite expansion at times t ≥ 0](abs-cable-sum-le.md)
- [For τ > 0, without the uniform mode a bound at rate k₁ for t ≥ 0](abs-cable-sum-le-of-zero-not-mem.md)
- [Splitting off the uniform mode of the finite expansion](cable-sum-insert-zero.md)
- [For τ > 0, the finite expansion decays to rest](tendsto-cable-sum.md)
- [For τ > 0 and ℓ, L ≠ 0, e^(t/τ) times the expansion tends to a₀](tendsto-exp-mul-cable-sum.md)
- [For L ≠ 0, cosine coefficients of the finite expansion](integral-cable-sum-mul-cos-mode.md)

## Mode coefficients of an arbitrary sealed solution

- [Cosine coefficient of a cable profile](mode-coeff.md)
- [For L > 0 and f′ = 0 at both ends, ∫ f″ φₙ = −(nπ/L)² ∫ f φₙ](integral-deriv-deriv-mul-cos-mode.md)
- [For L > 0, differentiating a mode coefficient under the integral sign](has-deriv-at-mode-coeff.md)
- [For L > 0, mode coefficients of sealed solutions evolve exponentially](mode-coeff-eq-mul-exp.md)

## The infinite eigenfunction expansion

- [Sealed-end mode expansion as an infinite series](cable-series.md)
- [For τ > 0 and t ≥ 0, absolutely summable aₙ give absolute convergence](summable-cable-series.md)
- [Initial profile of the infinite expansion](cable-series-time-zero.md)
- [For τ > 0 and absolutely summable aₙ, a uniform bound for t ≥ 0](abs-cable-series-le.md)
- [For τ > 0 and absolutely summable aₙ, the expansion decays to rest](tendsto-cable-series.md)
- [Termwise spatial derivative of the infinite expansion for t > 0](has-deriv-at-cable-series-space.md)
- [Spatial derivative function of the infinite expansion for t > 0](deriv-cable-series-space.md)
- [Termwise second spatial derivative of the expansion for t > 0](has-deriv-at-deriv-cable-series-space.md)
- [Termwise time derivative of the infinite expansion for t > 0](has-deriv-at-cable-series-time.md)
- [For absolutely summable aₙ, a cable solution at every t > 0](is-cable-solution-cable-series.md)
- [For absolutely summable aₙ, sealed ends at every t > 0](sealed-ends-cable-series.md)
- [For absolutely summable aₙ and t ≥ 0, cosine coefficients of the sum](integral-cable-series-mul-cos-mode.md)

## Consequences of the exponential evolution law

- [For τ > 0, the mode coefficients of a sealed solution tend to 0](tendsto-mode-coeff.md)
- [Total potential of a sealed solution evolves at the membrane rate](integral-eq-mul-exp.md)

## Steady state with a sealed far end, and the charging transient

- [Steady profile of a cable sealed at x = L](sealed-steady.md)
- [Slope of the sealed steady profile at each point](has-deriv-at-sealed-steady.md)
- [Slope function of the sealed steady profile](deriv-sealed-steady.md)
- [Curvature of the sealed steady profile](has-deriv-at-deriv-sealed-steady.md)
- [For ℓ ≠ 0, the sealed profile solves the steady cable equation](sealed-steady-steady.md)
- [The sealed steady profile has zero slope at x = L](deriv-sealed-steady-length.md)
- [Slope of the sealed steady profile at x = 0](deriv-sealed-steady-zero.md)
- [Charging transient of a cable sealed at x = L](charging-sum.md)
- [For τ ≠ 0 and ℓ ≠ 0, the charging transient solves the cable equation](is-cable-solution-charging-sum.md)
- [For L ≠ 0, the transient is sealed at L with a fixed slope at 0](deriv-charging-sum-ends.md)
- [For τ > 0, the charging transient tends to the steady profile](tendsto-charging-sum.md)

## Bounded coefficients at positive times

- [Time shift of the infinite expansion](cable-series-eq-shift.md)
- [For τ > 0, ε > 0 and ℓ, L ≠ 0, the mode factors are summable](summable-exp-neg-decay-rate.md)
- [Bounded coefficients give a solution of the cable equation for t > 0](is-cable-solution-cable-series-of-bounde.md)
- [Bounded coefficients give sealed ends for t > 0](sealed-ends-cable-series-of-bounded.md)
- [With bounded coefficients, the profile at t > 0 is continuous](continuous-cable-series-of-bounded.md)
- [Bounded coefficients: cosine coefficients of the expansion at t > 0](integral-cable-series-mul-cos-mode-of-bo.md)
- [With bounded coefficients, the expansion decays to rest](tendsto-cable-series-of-bounded.md)

## Green's function of the sealed cable: response to a localized input

- [Cosine coefficients of a unit point charge](green-coeff.md)
- [Uniform bound on the point-charge coefficients](abs-green-coeff-le.md)
- [Green's function of the sealed cable](sealed-green.md)
- [The sealed-cable Green's function solves the cable equation for t > 0](is-cable-solution-sealed-green.md)
- [The sealed-cable Green's function has sealed ends for t > 0](sealed-ends-sealed-green.md)
- [The sealed-cable Green's function is continuous in position for t > 0](continuous-sealed-green.md)
- [Cosine coefficients of the sealed-cable Green's function for t > 0](integral-sealed-green-mul-cos-mode.md)
- [For t > 0, the sealed-cable Green's function integrates to e^(−t/τ)](integral-sealed-green.md)
- [Reciprocity of the sealed-cable Green's function](sealed-green-comm.md)
- [The point-charge coefficients are even in the source](green-coeff-neg-source.md)
- [The point-charge coefficients are 2L-periodic in the source](green-coeff-add-two-mul-source.md)
- [The sealed-cable Green's function is even in the source](sealed-green-neg-source.md)
- [The sealed-cable Green's function is 2L-periodic in the source](sealed-green-add-two-mul-source.md)
- [Replacing L by −L negates the sealed-cable Green's function](sealed-green-neg-length.md)
- [For τ > 0, the sealed-cable Green's function decays to rest](tendsto-sealed-green.md)
- [Superposing point-charge responses reproduces the expansion for t > 0](integral-sealed-green-mul-cos-series.md)
- [Semigroup law of the sealed-cable Green's function](integral-sealed-green-mul-sealed-green.md)

## Green's function of the infinite cable

- [Green's function of the infinite cable](infinite-green.md)
- [At t > 0 the infinite-cable kernel solves the cable equation on ℝ](infinite-green-cable.md)
- [Restricted to a segment, the infinite-cable kernel is a cable solution](is-cable-solution-infinite-green.md)
- [For t > 0, the infinite-cable Green's function is positive](infinite-green-pos.md)
- [For t > 0, the infinite-cable kernel integrates to e^(−t/τ)](integral-infinite-green.md)
- [Symmetry of the infinite-cable Green's function](infinite-green-comm.md)
- [For t > 0, the infinite-cable kernel is largest at the input site](infinite-green-le.md)
- [Away from the input site, the infinite-cable kernel vanishes as t → 0⁺](tendsto-infinite-green-of-ne.md)
