# Running a stream for a positive duration keeps its mole fractions

For a [process stream](stream-flow.md) with species flow rates `ṅ i` and positive
[total flow](total.md), `0 < ∑ j, ṅ j`, and a positive duration `0 < Δt`, the
[mole fractions](../amount-of-substance-and-molar-mass/mole-fraction.md) of the
[accumulated amounts](integrate.md) `Δt * ṅ i` equal those of the flows:

`(Δt * ṅ i) / ∑ j, Δt * ṅ j = ṅ i / ∑ j, ṅ j` for every species `i`.

Under the positive total these are the entries of the stream's [composition](composition.md), so the
batch collected over any positive duration has the composition of the stream. The identity is the
case `α = Δt` of [mole fractions unchanged by a nonzero common factor](mole-fraction-rescale.md),
which needs only `Δt ≠ 0` and no condition on the total flow.
