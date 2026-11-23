# The MLE limit has smaller variance than the moment-estimator limit in every direction

Let `Y₁` be the Gaussian vector of `tendstoInDistribution_countMLE` (projections
`N(0, E ⟪ψ, t⟫²)`) and `Y₂` that of `tendstoInDistribution_mom` (projections `N(0, E ⟪g, t⟫²)`).
Under the information identity and the differentiated unbiasedness of the moment equations
(`inner_inverse_countFisherInfo_le`), for every direction `u`
`Var ⟪I⁻¹ Y₁, u⟫ ≤ Var ⟪-J⁻¹ Y₂, u⟫`: the joint MLE is asymptotically at least as efficient as the
method-of-moments estimator.
