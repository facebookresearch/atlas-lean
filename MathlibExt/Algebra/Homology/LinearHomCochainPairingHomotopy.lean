/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import MathlibExt.Algebra.Homology.GradedPairingHomology
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe w v u


namespace HomologicalComplex

open Opposite

variable (R : Type u) [CommRing R]
variable {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
variable [HasTensor K₁ K₂]
variable {M N P : ModuleCat.{u} R}

/-- Homotopic chain diagonals induce the same pairing on linear Hom-cohomology. -/
theorem linearHomCochainGradedPairing_pairHomology_eq_of_homotopy
    (Δ Γ : K₃ ⟶ tensorObj K₁ K₂) (h : Homotopy Δ Γ)
    (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    (linearHomCochainGradedPairing R Δ μ).pairHomology p q =
      (linearHomCochainGradedPairing R Γ μ).pairHomology p q := by
  let T := tensorObj K₁ K₂
  let C₁ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (Opposite.op K₁)
  let C₂ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj (Opposite.op K₂)
  let U := linearHomCochainGradedPairing R (𝟙 T) μ
  let PΔ := linearHomCochainGradedPairing R Δ μ
  let PΓ := linearHomCochainGradedPairing R Γ μ
  let fΔ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map Δ.op
  let fΓ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map Γ.op
  have hpairΔ : ∀ i j, U.pair i j ≫ fΔ.f (i + j) = PΔ.pair i j := by
    intro i j
    simpa [U, PΔ, fΔ, T] using
      (linearHomCochainGradedPairing_pair_comp R (𝟙 T) Δ μ i j)
  have hpairΓ : ∀ i j, U.pair i j ≫ fΓ.f (i + j) = PΓ.pair i j := by
    intro i j
    simpa [U, PΓ, fΓ, T] using
      (linearHomCochainGradedPairing_pair_comp R (𝟙 T) Γ μ i j)
  have hΔfac := CochainGradedPairing.pairHomology_naturality
    U PΔ (𝟙 C₁) (𝟙 C₂) fΔ (by
      intro i j
      rw [hpairΔ i j]
      rw [HomologicalComplex.id_f, HomologicalComplex.id_f,
        MonoidalCategory.id_tensorHom_id, Category.id_comp]) p q
  have hΓfac := CochainGradedPairing.pairHomology_naturality
    U PΓ (𝟙 C₁) (𝟙 C₂) fΓ (by
      intro i j
      rw [hpairΓ i j]
      rw [HomologicalComplex.id_f, HomologicalComplex.id_f,
        MonoidalCategory.id_tensorHom_id, Category.id_comp]) p q
  have hmap : homologyMap fΔ (p + q) = homologyMap fΓ (p + q) := by
    exact Homotopy.linearHomCochainComplex_homologyMap_eq R h P (p + q)
  have hΔfac' : PΔ.pairHomology p q =
      U.pairHomology p q ≫ homologyMap fΔ (p + q) := by
    simpa [C₁, C₂] using hΔfac
  have hΓfac' : PΓ.pairHomology p q =
      U.pairHomology p q ≫ homologyMap fΓ (p + q) := by
    simpa [C₁, C₂] using hΓfac
  exact hΔfac'.trans (((by rw [hmap]) :
    U.pairHomology p q ≫ homologyMap fΔ (p + q) =
      U.pairHomology p q ≫ homologyMap fΓ (p + q)).trans hΓfac'.symm)

end HomologicalComplex
