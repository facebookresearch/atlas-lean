# Mass composition, defined for positive molar masses and total flow

The mass composition of a [process stream](stream-flow.md) with species flow rates `ṅ i`, for a real
vector `M` of molar masses, is defined when every molar mass is positive, `0 < M i` for all `i`, and
the [total flow](total.md) is positive, `0 < ∑ j, ṅ j`. It is then the vector `w` of
[mass fractions](../amount-of-substance-and-molar-mass/mass-fraction.md) of the flows,
`w i = ṅ i * M i / ∑ j, ṅ j * M j`, whose denominator is positive since `0 ≤ ṅ i`
([positive total mass flow](../amount-of-substance-and-molar-mass/sum-amount-mul-molar-mass-pos.md)).
Otherwise, that is, when some molar mass is zero or negative or the total flow is zero (it is
[never negative](total-nonneg.md)), the mass composition is undefined; this includes every stream
over an empty species type.
