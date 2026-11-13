# Fisher Information

The **Fisher information operator** of the family `p` at `θ`: the second moment
`E_θ [s sᵀ]` of the score `s = score p θ` under the law `p θ ν` (the Bochner integral of the
rank-one operators `InnerProductSpace.rankOne ℝ s s : v ↦ ⟪s, v⟫ • s`), as a continuous linear
map `E →L[ℝ] E`. Its quadratic form is `⟪I(θ) u, u⟫ = E_θ ⟪s, u⟫²`
(`inner_fisherInformation_apply`). If the score is not square integrable the Bochner integral
takes its junk value `0`.
