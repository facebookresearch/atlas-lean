# Functional delta theorem

**Functional delta theorem** (van der Vaart, Theorem 20.8). Let `r n → ∞` and
`r n • (X n - θ) ⇒ G` in the normed space `E`, with `G ∈ E₀` almost surely and `X n ∈ D` almost
surely. If `φ` is Hadamard differentiable at `θ` tangentially to `E₀` with derivative `φ'`, then
`r n • (φ (X n) - φ θ) ⇒ φ' G`.

`E` need not be separable. The measurability of `r n • (φ (X n) - φ θ)` and of `φ' ∘ G` is
assumed (Borel framework); `functional_delta_of_continuous` derives both when `φ` and `φ'` are
continuous. The proof applies `extended_comp` to `g n y = r n • (φ (θ + (r n)⁻¹ • y) - φ θ)`.
