# Compensator identity in mean

**Compensator identity in mean** for the random-censorship model. Let the latent failure
time `T` and censoring time `C` be independent, `F` the law of `T` and `Λ` its hazard measure.
For every Borel set `B` of times,
`E[Λ(B ∩ (-∞, X])] = E[∫_B Y dΛ] = P(T ∈ B, T ≤ C) = E[∫_B dN]`:
the expected compensator mass of `B` equals the expected number of observed failures in `B`.
Independent censoring is used through `P(T ≥ s, C ≥ s) = F[s, ∞) G[s, ∞)`.
