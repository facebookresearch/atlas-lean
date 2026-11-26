/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHomotopy

/-!
# Homotopy naturality of module Hom cohomology pairings

Let R be a commutative ring and Kᵢ, Lᵢ nonnegative chain complexes of
R-modules in universe u. Fix Δ_K : K₃ → K₁ ⊗ K₂,
Δ_L : L₃ → L₁ ⊗ L₂ and a coefficient pairing μ : M ⊗[R] N → P.
For chain maps fᵢ : Lᵢ → Kᵢ, a homotopy
Δ_K ∘ f₃ ∼ (f₁ ⊗ f₂) ∘ Δ_L makes the induced cohomology pairing square
commute. Hom cohomology is contravariant in each chain complex, so the
vertical maps go from the K-cohomology groups to the L-cohomology groups.
Both indicated tensor products of chain complexes are required to exist.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace HomologicalComplex

/-- Let R be a commutative ring, Kᵢ and Lᵢ nonnegative chain complexes of
R-modules, and fᵢ : Lᵢ → Kᵢ chain maps. Suppose K₁ ⊗ K₂ and L₁ ⊗ L₂
exist, and the diagonals Δ_K : K₃ → K₁ ⊗ K₂ and
Δ_L : L₃ → L₁ ⊗ L₂ satisfy a homotopy
Δ_K ∘ f₃ ∼ (f₁ ⊗ f₂) ∘ Δ_L. For any R-linear coefficient pairing
μ : M ⊗[R] N → P and p, q ∈ ℕ, the cohomology pairings satisfy
pair_L ∘ (Hᵖ(f₁*) ⊗ Hᑫ(f₂*)) = Hᵖ⁺ᑫ(f₃*) ∘ pair_K,
where each fᵢ* is precomposition on Hom cochains. -/
theorem linearHomCochainGradedPairing_pairHomology_naturality_of_homotopy
    (R : Type u) [CommRing R]
    {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {L₁ L₂ L₃ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor L₁ L₂]
    {M N P : ModuleCat.{u} R}
    (ΔK : K₃ ⟶ tensorObj K₁ K₂) (ΔL : L₃ ⟶ tensorObj L₁ L₂)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : L₃ ⟶ K₃)
    (hΔ : @_root_.Homotopy ℕ (ModuleCat.{u} R) _ _ (ComplexShape.down ℕ)
      L₃ (tensorObj K₁ K₂) (f₃ ≫ ΔK) (ΔL ≫ tensorHom f₁ f₂))
    (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    (homologyMap
          ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).map f₁.op) p ⊗ₘ
        homologyMap
          ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).map f₂.op) q) ≫
      (linearHomCochainGradedPairing R ΔL μ).pairHomology p q =
    (linearHomCochainGradedPairing R ΔK μ).pairHomology p q ≫
      homologyMap
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map f₃.op)
        (p + q) := by
  let F₁ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).map f₁.op
  let F₂ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).map f₂.op
  let F₃ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map f₃.op
  let PΓ := linearHomCochainGradedPairing R (f₃ ≫ ΔK) μ
  let PΘ := linearHomCochainGradedPairing R (ΔL ≫ tensorHom f₁ f₂) μ
  have hleft :
      (homologyMap F₁ p ⊗ₘ homologyMap F₂ q) ≫
          (linearHomCochainGradedPairing R ΔL μ).pairHomology p q =
        PΘ.pairHomology p q := by
    let I₃ :
        (linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).obj (op L₃) ⟶
          (linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).obj (op L₃) := 𝟙 _
    have hpair (i j : ℕ) :
        PΘ.pair i j ≫ I₃.f (i + j) =
          (F₁.f i ⊗ₘ F₂.f j) ≫
            (linearHomCochainGradedPairing R ΔL μ).pair i j := by
      dsimp [PΘ, F₁, F₂, I₃]
      simpa using linearHomCochainGradedPairing_naturality R
        (ΔL ≫ tensorHom f₁ f₂) ΔL f₁ f₂ (𝟙 L₃)
        (by
          change ΔL ≫ tensorHom f₁ f₂ = ΔL ≫ tensorHom f₁ f₂
          rfl) μ i j
    have h := CochainGradedPairing.pairHomology_naturality
      PΘ (linearHomCochainGradedPairing R ΔL μ) F₁ F₂ I₃ hpair p q
    simpa [I₃] using h
  have hright :
      PΓ.pairHomology p q =
        (linearHomCochainGradedPairing R ΔK μ).pairHomology p q ≫
          homologyMap F₃ (p + q) := by
    let I₁ :
        (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (op K₁) ⟶
          (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (op K₁) := 𝟙 _
    let I₂ :
        (linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj (op K₂) ⟶
          (linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj (op K₂) := 𝟙 _
    have hpair (i j : ℕ) :
        (linearHomCochainGradedPairing R ΔK μ).pair i j ≫ F₃.f (i + j) =
          (I₁.f i ⊗ₘ I₂.f j) ≫ PΓ.pair i j := by
      dsimp only [PΓ, F₃, I₁, I₂]
      simpa only [HomologicalComplex.id_f,
        MonoidalCategory.id_tensorHom_id, Category.id_comp] using
        (linearHomCochainGradedPairing_pair_comp R ΔK f₃ μ i j)
    have h := CochainGradedPairing.pairHomology_naturality
      (linearHomCochainGradedPairing R ΔK μ) PΓ I₁ I₂ F₃ hpair p q
    simpa [I₁, I₂] using h
  rw [hleft]
  change
    (linearHomCochainGradedPairing R (ΔL ≫ tensorHom f₁ f₂) μ).pairHomology p q = _
  rw [← linearHomCochainGradedPairing_pairHomology_eq_of_homotopy
    R (f₃ ≫ ΔK) (ΔL ≫ tensorHom f₁ f₂) hΔ μ p q]
  exact hright

end HomologicalComplex
