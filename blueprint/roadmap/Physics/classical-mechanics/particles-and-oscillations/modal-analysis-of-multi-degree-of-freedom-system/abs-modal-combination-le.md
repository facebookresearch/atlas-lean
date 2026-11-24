# Absolute-sum bound on a combination of modal responses

Let `n` be a finite set, `M` and `Φ` real `n × n` matrices, `r ∈ ℝⁿ` with
[participation factors](participation.md) `Γ = Φᵀ M r`, `T` a real number, `c : n → ℝ`
coefficients, and `u, q : n → (ℝ → ℝ)` such that every `u_j` is continuous on `[0, T]` and
`q_j(t) = Γ_j u_j(t)` for every `j` and every `t ∈ [0, T]`. Then for every `t ∈ [0, T]`,

`|∑_j c_j q_j(t)| ≤ ∑_j |c_j Γ_j| S_j`,

where `S_j` is the [spectral displacement](spectral-displacement.md) of `u_j` on `[0, T]`. In the
base-motion reading `u_j` is the reference response of mode `j` and the relation `q_j = Γ_j u_j` is
an input, not derived.
