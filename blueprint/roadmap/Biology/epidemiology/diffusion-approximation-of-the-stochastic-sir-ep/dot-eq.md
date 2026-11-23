# Duality identity

**Duality identity** (the integration-by-parts Wiener integral). If `y` solves the adjoint
equation `y' = -DF(x)ᵀ y` on `[0, t]`, then for the fluctuation path driven by `m`,
`⟨y(t), U(t)⟩ = ⟨y(0), u₀⟩ + ⟨y(t), m(t) - m(0)⟩ + ∫₀ᵗ ⟨DF(x(s))ᵀ y(s), m(s) - m(0)⟩ ds`.
The last two terms are `∫₀ᵗ ⟨y(s), dm(s)⟩`, integrated by parts.
