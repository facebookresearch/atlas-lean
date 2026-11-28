# Phi NModule

A `(φ, N)`-module structure on a `K₀`-module `D`, for a ring automorphism `σ` of the field
`K₀` (with inverse `σ'`) and a scalar `p ∈ K₀`: a bijective `σ`-semilinear map `φ : D → D` (a
`σ`-semilinear equivalence) and a `K₀`-linear map `N : D → D` with `N (φ x) = p • φ (N x)` for all
`x : D`.

Fontaine–Ouyang (Definition 8.13) also require `D` to be finite-dimensional; here that is a
separate hypothesis `[FiniteDimensional K₀ D]` wherever it is used.
