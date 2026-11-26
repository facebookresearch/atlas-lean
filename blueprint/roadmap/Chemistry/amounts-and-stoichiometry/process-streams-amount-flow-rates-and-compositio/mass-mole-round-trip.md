# Mole-to-mass-to-mole conversion returns a stream's mole fractions

For a [process stream](stream-flow.md) with species flow rates `ṅ i`, positive
[total flow](total.md), `0 < ∑ j, ṅ j`, and molar masses `0 < M i` for every species `i`, let
`x i = ṅ i / ∑ j, ṅ j` be the
[mole fractions](../amount-of-substance-and-molar-mass/mole-fraction.md) of its flows. Converting
`x` to mass fractions, `w i = x i * M i / ∑ j, x j * M j` (the
[mass-fraction](../amount-of-substance-and-molar-mass/mass-fraction.md) formula applied to `x` in
place of amounts), and then `w` back to mole fractions, `(w i / M i) / ∑ j, w j / M j`
([mole fractions computed from mass fractions](../amount-of-substance-and-molar-mass/mole-fraction-of-mass-fraction.md)),
returns `x`. All denominators are positive under these hypotheses. This is the
[round trip for mole fractions on the simplex](../amount-of-substance-and-molar-mass/mole-fraction-of-mass-fraction-mass-frac-2.md)
applied to the stream's mole fractions, which are nonnegative and sum to `1`.
