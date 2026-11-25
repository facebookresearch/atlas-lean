/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneous
public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace HomologicalComplex

open LinearHomCochainPairingHeterogeneous

variable (R : Type u) [CommRing R]

noncomputable local instance linearHomCochainChainUnitMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- The cochain-chain descriptor agrees with the heterogeneous pairing descriptor
when the second cochain is the identity. -/
lemma linearHomCochainChainPairDesc_eq_linearHomPairingDesc
    {K₁ K₂ L : ChainComplex (ModuleCat.{u} R) ℕ}
    {A : ModuleCat.{u} R} [HasTensor K₁ K₂]
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ) (φ : K₁.X p ⟶ A) :
    linearHomCochainChainPairDesc R ρ p q φ =
      linearHomPairingDesc R (ρ q) p q φ (𝟙 (K₂.X q)) := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearHomCochainChainPairDesc
  rw [ι_mapBifunctorDesc, ιTensorObj_comp_linearHomPairingDesc]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp
  · simp [hi]

/-- A compatible chain counit and coefficient action make the induced
linear-Hom cochain-chain pairing left-unital in every natural degree. -/
theorem linearHomCochainChainPair_left_unit_of_diagrams
    {Kᵤ K : ChainComplex (ModuleCat.{u} R) ℕ}
    {U : ModuleCat.{u} R}
    (Δ : K ⟶ tensorObj Kᵤ K)
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U)
    (ρ : ∀ q, U ⊗ K.X q ⟶ K.X q)
    (hΔ : Δ ≫ tensorHom ε (𝟙 K) ≫ (leftUnitor K).hom = 𝟙 K)
    (hρ : ∀ q, (e ▷ K.X q) ≫ ρ q = (λ_ (K.X q)).hom)
    (q : ℕ) :
    (linearHomCochainUnitOfCounitHom R Kᵤ ε U e ▷ K.X q) ≫
        (𝟙 _ ⊗ₘ (K.XIsoOfEq (Nat.zero_add q)).inv) ≫
        linearHomCochainChainPair R Δ ρ 0 q =
      (λ_ (K.X q)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a x
  change R at a
  change (linearHomCochainChainPair R Δ ρ 0 q).hom
      ((a • linearHomCochainUnitOfCounit R Kᵤ ε U e) ⊗ₜ[R]
        ((K.XIsoOfEq (Nat.zero_add q)).inv).hom x) = a • x
  rw [← TensorProduct.smul_tmul']
  rw [map_smul]
  congr 1
  rw [linearHomCochainChainPair_tmul,
    linearHomCochainChainPairDesc_eq_linearHomPairingDesc]
  have htransport {m n : ℕ} (h : m = n) :
      (K.XIsoOfEq h).inv = (K.XIsoOfEq h.symm).hom := by
    subst n
    rfl
  have hdesc := heterogeneousLinearHomPairingDesc_left_unit R ε e (ρ q)
    (𝟙 (K.X q)) (by simpa using hρ q) q (𝟙 (K.X q))
  simp only [Category.comp_id] at hdesc
  have hmain :
      (K.XIsoOfEq (Nat.zero_add q)).inv ≫ Δ.f (0 + q) ≫
          linearHomPairingDesc R (ρ q) 0 q
            (linearHomCochainUnitOfCounit R Kᵤ ε U e) (𝟙 (K.X q)) =
        𝟙 (K.X q) := by
    rw [htransport]
    rw [XIsoOfEq_comp_heterogeneousLinearHomPairingDesc R Δ (ρ q)
      0 q q (Nat.zero_add q).symm
      (linearHomCochainUnitOfCounit R Kᵤ ε U e) (𝟙 (K.X q))]
    rw [hdesc]
    have hΔq := congrArg (fun f => f.f q) hΔ
    dsimp only [HomologicalComplex.comp_f] at hΔq
    change Δ.f q ≫ (ε ▷ K).f q ≫ (λ_ K).hom.f q = 𝟙 (K.X q) at hΔq
    exact hΔq
  exact ConcreteCategory.congr_hom hmain x

end HomologicalComplex

end
