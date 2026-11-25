# Map comp

Successive bundled maps compose into one map: coalgebra morphisms compose
contravariantly as `ψ₁ ≫ ψ₂` while algebra morphisms compose covariantly as
`φ₂ ≫ φ₁`, exactly matching the `map_tau` orientation. The proof unfolds both
sides with `map_tau`, splits the morphism cochains with `ofHom_comp`, and
reassociates the degree-zero factors with the pinned cochain associativity
lemmas.
