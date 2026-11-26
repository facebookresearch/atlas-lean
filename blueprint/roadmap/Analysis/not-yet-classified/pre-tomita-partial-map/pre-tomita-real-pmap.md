# Real-linear partial pre-Tomita map

Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put `D_φ={x ∈ n_φ
: x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`.
`preTomitaRealPMap φ : H_φ →ₗ.[ℝ] H_φ` has domain `C_φ` with scalars restricted to `ℝ`, and
value `S₀Λ(x)=Λ(x*)`. The Hilbert norm and topology are unchanged.
