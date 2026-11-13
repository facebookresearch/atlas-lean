# Nb Avg Log Lik

The averaged joint log-likelihood of the first `n` observations of a sample with covariate rows
`x i ω`, offsets `o i ω` and counts `y i ω`, at `p = (β, θ)`:
`n⁻¹ ∑_{i<n} nbLogPmf θ (y i ω) (x i ω ⬝ᵥ β + o i ω)`. It is `n⁻¹ • nbJointLogLik` of the
`n`-row design (`nbAvgLogLik_eq_nbJointLogLik`).
