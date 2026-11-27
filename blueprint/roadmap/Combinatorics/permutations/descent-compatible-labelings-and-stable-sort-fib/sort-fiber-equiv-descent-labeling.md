# Sorting fibers are descent labelings

For `n,m : ℕ` and `σ ∈ S_n`, the fiber `{f : Fin n → Fin m // Tuple.sort f = σ}` is equivalent
to `DescentLabeling σ m`. The forward map is `f ↦ f ∘ σ`; the inverse is `g ↦ g ∘ σ⁻¹`. This
includes `n=0`.
