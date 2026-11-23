# Asymptotic normality of the joint count MLE, information form

Under the hypotheses of
`tendstoInDistribution_countMLE` and the information identity `E ⟪ψ, t⟫² = ⟪I t, t⟫`
(`ψ = countScore σ θ₀ K`, `I = countFisherInfo a b σ τ`), `√n (θhat n - θ₀) → I⁻¹ Y` with
`Y ~ N(0, I)`, so the limit is `N(0, I⁻¹)` (`hasLaw_inner_inverse_countFisherInfo`).
