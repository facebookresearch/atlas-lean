# Aipw Score bias gateaux zero

Finite Neyman orthogonality: the AIPW bias has zero Gateaux derivative at
the true nuisances along any fixed direction.

Informal clause map: "finite covariate space" is `[Finite 𝒳]` (with
`[MeasurableSpace 𝒳]` and `[MeasurableSingletonClass 𝒳]`, and `Fintype 𝒳`
supplied locally by `Fintype.ofFinite`); "missing at random"
is `hmar : MissingAtRandom μ R Y X`; "response positivity" is
`hpos : ResponsePositivity μ R X`; "true nuisances as base point" is
`propensity μ R X` and `outcomeRegression μ Y X`; "any fixed direction" is
`δm δe : 𝒳 → ℝ`; "zero first-order Gateaux derivative at `t = 0`" is
`HasDerivAt … 0 0`.
