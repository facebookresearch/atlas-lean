# Composition of process streams

Process streams as nonnegative species flow rates over a finite species type: their total flow,
their mole composition, defined only for a positive total flow, and their mass composition, defined
only for positive molar masses and a positive total flow; the amounts a stream accumulates over a
duration; rescaling by a nonnegative factor; and the species balance of an inlet and an outlet
stream.

## Streams and totals

- [Process stream with nonnegative species flow rates](stream-flow.md)
- [Zero stream](zero.md)
- [Total amount-flow rate of a stream](total.md)
- [Total flow of the zero stream is zero](zero-total.md)
- [Total flow of a stream is nonnegative](total-nonneg.md)
- [Total flow is zero exactly when every species flow is zero](total-eq-zero-iff.md)

## Mole composition of a stream

- [Mole composition of a stream, defined only for positive total flow](composition.md)
- [With positive total flow, the composition is the mole fractions](composition-eq-mole-fraction.md)
- [A stream has no composition exactly when its total flow is zero](composition-eq-none-iff.md)
- [The zero stream has no composition](zero-composition.md)
- [The composition of a stream sums to one](sum-composition.md)

## Amounts accumulated over a duration

- [Amounts accumulated by running a constant stream for a duration](integrate.md)
- [Running a stream for zero duration accumulates zero amounts](integrate-zero.md)
- [Total accumulated amount is the duration times the total flow](sum-integrate.md)
- [Running a stream for a positive duration keeps its mole fractions](composition-of-integrate.md)

## Mass flows and mass composition

- [Mass-flow rates of a stream from molar masses](mass-flow.md)
- [Mass fractions of a stream are its mass flows over their total](mass-fraction-eq-mole-fraction-mass-flow.md)
- [Mass composition, defined for positive molar masses and total flow](mass-composition.md)
- [A nonpositive molar mass leaves a stream without mass composition](mass-composition-eq-none-of-nonpos-at.md)
- [Positive total mass flow](sum-mass-flow-pos.md)
- [Without positive total mass flow, a stream has no mass composition](mass-composition-eq-none-of-sum-nonpos.md)
- [Mass composition is mass fractions for positive masses and total flow](mass-composition-eq-mass-fraction.md)
- [The mass composition of a stream sums to one](sum-mass-composition.md)
- [Mole-to-mass-to-mole conversion returns a stream's mole fractions](mass-mole-round-trip.md)
- [Mass-to-mole-to-mass conversion returns a stream's mass fractions](mole-mass-round-trip.md)

## Rescaling and species balances

- [Rescaling a stream's flows by a nonnegative factor](rescale.md)
- [Rescaling a stream multiplies its total flow by the factor](total-rescale.md)
- [Species balance: inflow minus outflow plus generation is accumulation](is-balance.md)
- [A species balance is invariant under positive rescaling of all terms](balance-rescale-iff.md)
- [Mole fractions of a stream are unchanged by a nonzero common factor](mole-fraction-rescale.md)
- [Positive rescaling preserves a stream's composition](composition-rescale.md)
