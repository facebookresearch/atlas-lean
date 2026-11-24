# Mole fractions of a stream are unchanged by a nonzero common factor

For every [process stream](stream-flow.md) with species flow rates `ṅ i` and every real `α ≠ 0`,
positive or negative, multiplying every flow rate by `α` leaves the
[mole fractions](../amount-of-substance-and-molar-mass/mole-fraction.md) unchanged:

`(α * ṅ i) / ∑ j, α * ṅ j = ṅ i / ∑ j, ṅ j` for every species `i`.

No condition on the total flow is needed: when it is `0`, both sides are `0` by the convention
`x / 0 = 0`. For `α < 0` the scaled vector has nonpositive entries, so it is not a stream unless
every flow is `0`; the identity concerns the mole-fraction formula.
