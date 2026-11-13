# The sample variance of a finite i.i.d. family is integrable and unbiased

For
`n ≥ 2` independent, identically distributed, square-integrable real observations
`X i`, `i : Fin n`, with common law that of `X i0`, the sample variance
`s² = FiniteProbability.sampleVarUnbiased (fun i => X i ω) = (n - 1)⁻¹ ∑ᵢ (Xᵢ - X̄)²`,
`X̄ = n⁻¹ ∑ⱼ Xⱼ`, is integrable and `E s² = Var (X i0)`.
