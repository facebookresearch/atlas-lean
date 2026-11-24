# Mole composition of a stream, defined only for positive total flow

The mole composition of a [process stream](stream-flow.md) with species flow rates `ṅ i` is defined
when its [total flow](total.md) is positive, `0 < ∑ j, ṅ j`, and is then the vector `x` of
[mole fractions](../amount-of-substance-and-molar-mass/mole-fraction.md) of the flows,
`x i = ṅ i / ∑ j, ṅ j`; otherwise it is undefined, so no division by a zero total occurs. Since the
flows are nonnegative, the composition is undefined exactly when the total flow is zero, that is,
when every species flow is zero
([no composition exactly at zero total flow](composition-eq-none-iff.md)); this includes every
stream over an empty species type.
