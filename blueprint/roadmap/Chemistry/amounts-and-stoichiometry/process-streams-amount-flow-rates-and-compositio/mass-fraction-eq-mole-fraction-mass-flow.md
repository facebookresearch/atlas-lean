# Mass fractions of a stream are its mass flows over their total

For every [process stream](stream-flow.md) with species flow rates `ṅ i` and every real vector `M`
(molar masses in the physical reading), the
[mass fractions](../amount-of-substance-and-molar-mass/mass-fraction.md) of the flows are the
[mole-fraction formula](../amount-of-substance-and-molar-mass/mole-fraction.md) applied to the
[mass flows](mass-flow.md) `ṁ i = ṅ i * M i`:

`ṅ i * M i / ∑ j, ṅ j * M j = ṁ i / ∑ j, ṁ j` for every species `i`.

The two sides are the same expression, so the identity holds for every `M`. When the total mass flow
`∑ j, ṁ j` is `0`, for example for the zero stream, both sides are `0` by the convention
`x / 0 = 0`.
