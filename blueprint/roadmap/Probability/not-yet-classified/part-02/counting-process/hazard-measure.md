# Hazard Measure

The **hazard measure** `dΛ(s) = dF(s) / F[s, ∞)` of a law `F` on `ℝ`, i.e. the cumulative
hazard `Λ(t) = ∫_{(-∞, t]} dF(s) / F([s, ∞))` as a measure. For a law with a density `f` it is
`λ(s) ds` with hazard rate `λ = f / S(s-)` (`hazardMeasure_withDensity`); an atom of `F` at `s`
gives `Λ` the atom `F{s} / F[s, ∞) ≤ 1`. Convention `0⁻¹ = ∞`: the density is infinite where
`F[s, ∞) = 0`, a set of `F`-measure zero (`ae_measure_Ici_ne_zero`).
