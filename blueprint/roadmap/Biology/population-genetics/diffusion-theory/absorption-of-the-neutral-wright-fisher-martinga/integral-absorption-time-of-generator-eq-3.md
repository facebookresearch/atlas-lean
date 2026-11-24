# Integral absorption Time of generator eq neg of tendsto Uniformly On

Stability of the neutral stopped-occupation identity under uniform limits.

If smooth potentials `u n` with integrands `g n` satisfy the hypotheses of
`integral_absorptionTime_of_generator_eq_neg` for every `n`, and converge uniformly on
`Set.Icc 0 1` to `uInf` and `gInf`, then the stopped occupation of `gInf` is integrable
and its expectation is `uInf x`, for starting points `x` in `[0, 1]`.

The `x ∈ Set.Icc 0 1` hypothesis is included explicitly for readability, since uniform
convergence on `[0, 1]` controls the limit only there; it in fact follows from the
range condition and the almost-everywhere initial condition, since the measure is a
probability measure.

This is a closure statement only: it assumes approximants and uniform convergence, and
claims nothing about approximability of any particular Green potential, no
occupation-density identity, and no nonzero selection.
