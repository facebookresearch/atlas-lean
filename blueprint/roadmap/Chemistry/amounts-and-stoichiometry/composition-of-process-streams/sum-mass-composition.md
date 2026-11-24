# The mass composition of a stream sums to one

For a [process stream](stream-flow.md) with species flow rates `ṅ i` and molar masses `0 < M i` for
every species `i`, if the [mass composition](mass-composition.md) is defined and equal to `w`, then
`∑ i, w i = 1`. The mass composition is defined only when every molar mass is positive and the total
flow is positive, and is then the vector of mass fractions `w i = ṅ i * M i / ∑ j, ṅ j * M j`, whose
denominator is positive because the flows satisfy `0 ≤ ṅ j`, and whose entries sum to `1`
([mass fractions sum to one](../amount-of-substance-and-molar-mass/sum-mass-fraction.md)). A stream
with zero total flow has no mass composition, and the statement says nothing about it.
