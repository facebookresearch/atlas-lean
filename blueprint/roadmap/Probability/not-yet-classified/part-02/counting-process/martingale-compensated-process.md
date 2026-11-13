# Compensator identity (martingale form)

In the random-censorship model with latent failure
time `T` independent of the censoring time `C`, the compensated counting process
`M(t) = N(t) - ∫_{(-∞, t]} Y dΛ`, with `Λ` the hazard measure of the law of `T`, is a martingale
for the history filtration `ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)`. So `A(t) = ∫_{(-∞, t]} Y dΛ`, which is
`ℱ_{t-}`-measurable (`measurable_compensator_strictPast`), is a compensator of `N` in the sense
that `N - A` is a martingale and `A(t)` is `ℱ_{t-}`-measurable (uniqueness is not proved), and the
intensity is `Y(t) dΛ(t)` (`Y(t) λ(t) dt` when `T` has a density, `hazardMeasure_withDensity`).
