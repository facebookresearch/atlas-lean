/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: Avocado
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import MathlibExt.Algebra.Homology.GradedPairingHomology
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing

/-!
# Homotopy invariance of Hom cohomology pairings

Homotopic tensor diagonals induce the same pairing on Hom cohomology over a commutative
ring. The result holds in every pair of nonnegative degrees and uses the original chain
complexes, coefficient modules and tensor total, without projective-resolution assumptions.
-/

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

/-- Let R be a commutative ring, K₁, K₂, K₃ nonnegative chain complexes of
R-modules with K₁ ⊗ K₂ defined, and μ : M ⊗[R] N → P an R-linear
coefficient pairing. If the chain maps Δ, Γ : K₃ → K₁ ⊗ K₂ are homotopic,
then their induced pairings
Hᵖ(Hom_R(K₁; M)) ⊗[R] Hᑫ(Hom_R(K₂; N)) → Hᵖ⁺ᑫ(Hom_R(K₃; P))
are equal for every p, q ∈ ℕ. -/
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
