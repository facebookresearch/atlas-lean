# Core coefficient belongs to its generated von Neumann algebra

Let `A` be a nonunital
complex C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive,
nonnegative-real homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`.
Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the
seminorm `√q(x)`, with dense complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0
→ a=0` for every positive `a : A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with
linear equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. each bounded left operator
`λ_φ(ξ)=tomitaCoreLeftRepresentation φ ξ`, for `ξ ∈ C_φ`, belongs to
`tomitaCoreGeneratedVonNeumannAlgebra φ`.
