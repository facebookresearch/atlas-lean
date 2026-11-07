# Expected time to the first coalescence

The expected time to the first coalescence among `m` lineages,
`c_m = ∫_0^∞ exp(-C(m,2) R(s)) ds`, in a population of relative size `η`
(Bhaskar & Song's `E[T_{m,m}]`). When the integrand is not integrable (for example `η ≡ 0`),
this is Lean's junk value `0`; for piecewise-constant histories it is integrable
(`choose_two_mul_firstCoalMean`).
