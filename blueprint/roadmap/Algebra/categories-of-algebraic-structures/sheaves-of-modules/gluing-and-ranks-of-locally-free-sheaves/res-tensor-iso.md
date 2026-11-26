# Tensor comparison for restriction to a slice

Let `C₀ : Type u` have morphism universe `u`, `J₀` be a topology, and `R₀` a commutative ring
sheaf. Assume monoidal additive sheafification and the locally-bijective comparison, with
additive sheafification and underlying-ring sheaf comparisons on the slice sites. For `U∈C₀`,
put `F_U=RestrictSheafification.restrictSheaf R₀ U`. The isomorphism `resTensorIso R₀ U A B`
has direction `F_U(A ⊗ B) ≅ F_U(A) ⊗ F_U(B)` for module sheaves `A,B`.
