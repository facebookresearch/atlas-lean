# Squared-error decomposition

For `W` with a finite second moment and any target `c`,
`E (W - c)² = E (μ[W | m] - c)² + E (W - μ[W | m])²`. This is the Pythagorean identity
`MeasureTheory.integral_sq_sub_eq_integral_sq_sub_condExp_add` with the constant predictor
`fun _ => c`, with the two summands commuted; it is not a second Pythagorean proof.
