# Chernoff bound for the empirical mean of real-valued i.i.d. variables

**Chernoff bound for the empirical mean of real-valued i.i.d. variables**,
in event form: if on the event `E` the empirical mean
`(1/n) ∑_{i<n} Xᵢ` satisfies the threshold inequality
`a ≤ t * (empirical mean) - log (mgf of X₁ at t)`, then
`μ(E) ≤ exp(-n * a)`.

Assume a probability measure, measurable independent identically distributed
coordinates, and integrability of `exp (t * X₀)`.

This is the one-dimensional core of the Cramér upper bound. The proof splits
on the sign of `t`: for `t > 0` it applies Mathlib's upper-tail Chernoff bound
to the sum `Sₙ`, and for `t < 0` the lower-tail Chernoff bound; in both cases
the exponential moment of the sum factors as `(mgf of X₁ at t)^n` by
independence and identical distribution.
