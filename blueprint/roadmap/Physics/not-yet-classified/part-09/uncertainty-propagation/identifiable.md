# Identifiable

Linear-algebraic identifiability of the calibration model `y = A *ᵥ θ`:
injectivity of `θ ↦ A *ᵥ θ`. This is injectivity of the design matrix as a linear
map, distinct from statistical identification of estimands (`IsIdentifiedBy`).
Unique-estimate claims are PROHIBITED without this hypothesis: see
`exists_distinct_of_nontrivial_ker`.
