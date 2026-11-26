# Semilinear maps as morphisms into scalar restriction

Let `R : Type r` be a ring, `S : Type s` a commutative ring, `σ : R →+* S`, `M :
ModuleCat.{vM} R`, and `N : ModuleCat.{vM} S`. The `S`-linear equivalence `(M →ₛₗ[σ] N) ≃ₗ[S]
(M ⟶ (restrictScalars σ).obj N)` preserves the underlying function in both directions. The
coefficient `S`-action on the restricted Hom space uses the commuting `R`- and `S`-actions on
`N` induced by `σ`.
