# Mass-to-mole-to-mass conversion returns a stream's mass fractions

For a [process stream](stream-flow.md) with species flow rates `ṅ i`, positive
[total flow](total.md), `0 < ∑ j, ṅ j`, and molar masses `0 < M i` for every species `i`, let
`w i = ṅ i * M i / ∑ j, ṅ j * M j` be the
[mass fractions](../amount-of-substance-and-molar-mass/mass-fraction.md) of its flows. Converting
`w` to mole fractions, `x i = (w i / M i) / ∑ j, w j / M j`
([mole fractions computed from mass fractions](../amount-of-substance-and-molar-mass/mole-fraction-of-mass-fraction.md)),
and then `x` back to mass fractions, `x i * M i / ∑ j, x j * M j`, returns `w`. All denominators are
positive under these hypotheses. This is the
[round trip for mass fractions on the simplex](../amount-of-substance-and-molar-mass/mass-fraction-mole-fraction-of-mass-frac.md)
applied to the stream's mass fractions, which are nonnegative and sum to `1`.
