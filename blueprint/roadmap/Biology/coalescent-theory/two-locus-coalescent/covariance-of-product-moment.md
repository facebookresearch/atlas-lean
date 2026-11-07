# Covariance of coalescence times

**Covariance of coalescence times** (Hudson 1983; Kaplan & Hudson 1985). Let `mA`, `mB`
solve the mean equations of the two loci and `f` the product-moment equations (`f i = 0` where
either locus has coalesced, `(Q f) i = -(mA i + mB i)` where neither has). Then `f - mA mB` is
`(ρ + 18) / (ρ² + 13ρ + 18)` from `linked`, `6 / (ρ² + 13ρ + 18)` from `partlySplit` and
`4 / (ρ² + 13ρ + 18)` from `split`. This is a statement about the backward equations; that their
solutions are the path-space moments of the chain is proved in `TwoLocusCoalescentPath`.
