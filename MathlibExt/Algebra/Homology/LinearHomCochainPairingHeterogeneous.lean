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

public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneousEngine

/-!
# Associativity and units from compatible Hom pairing diagrams

Let R be a commutative ring and work with nonnegative chain complexes and
coefficient modules in ModuleCat R, with carriers in universe u. The Hom
cochain complex has degree n term Hom_R(K_n, M). Its pairings are induced
by chain maps into total tensor products and coefficient tensor pairings.

Associativity allows distinct intermediate and output objects. With
c : Kᵣ → Kₗ and a : Mₗ → Mᵣ, the chain maps satisfy
α ∘ (Δ₁₂ ⊗ id) ∘ Δₗ ∘ c = (id ⊗ Δ₂₃) ∘ Δᵣ, and the coefficient maps satisfy
a ∘ μₗ ∘ (μ₁₂ ⊗ id) = μᵣ ∘ (id ⊗ μ₂₃) ∘ α.
These two equations imply associativity of the Hom cochain pairings after
precomposition by c, postcomposition by a, and the identification
(p + q) + r = p + (q + r).

For a chain map ε : Kᵤ → R[0] and a coefficient map e : R → U, the
degree-zero cochain e ∘ ε₀ is a left or right unit when the corresponding
chain counit and coefficient unit diagrams commute. The resulting identities
use the tensor unitors and identify 0 + q = q or p + 0 = p.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace HomologicalComplex

open LinearHomCochainPairingHeterogeneous

variable (R : Type u) [CommRing R]

noncomputable local instance linearHomHeterogeneousLawsChainComplexMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

theorem linearHomCochainPair_associativity_of_diagrams
    {K₁ K₂ K₃ K₁₂ K₂₃ Kₗ Kᵣ :
      ChainComplex (ModuleCat.{u} R) ℕ}
    {M₁ M₂ M₃ M₁₂ M₂₃ Mₗ Mᵣ : ModuleCat.{u} R}
    (Δ₁₂ : K₁₂ ⟶ K₁ ⊗ K₂) (Δₗ : Kₗ ⟶ K₁₂ ⊗ K₃)
    (Δ₂₃ : K₂₃ ⟶ K₂ ⊗ K₃) (Δᵣ : Kᵣ ⟶ K₁ ⊗ K₂₃)
    (c : Kᵣ ⟶ Kₗ)
    (μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂) (μₗ : M₁₂ ⊗ M₃ ⟶ Mₗ)
    (μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃) (μᵣ : M₁ ⊗ M₂₃ ⟶ Mᵣ)
    (a : Mₗ ⟶ Mᵣ)
    (hΔ : c ≫ Δₗ ≫ (Δ₁₂ ▷ K₃) ≫ (α_ K₁ K₂ K₃).hom =
      Δᵣ ≫ (K₁ ◁ Δ₂₃))
    (hμ : (μ₁₂ ▷ M₃) ≫ μₗ ≫ a =
      (α_ M₁ M₂ M₃).hom ≫ (M₁ ◁ μ₂₃) ≫ μᵣ)
    (p q r : ℕ) :
    ((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q ⊗ₘ
        𝟙 ((linearHomCochainComplex R K₃ M₃).X r)) ≫
      (linearHomCochainGradedPairing R Δₗ μₗ).pair (p + q) r ≫
      (linearHomCochainComparison R c a).f ((p + q) + r) ≫
      ((linearHomCochainComplex R Kᵣ Mᵣ).XIsoOfEq
        (Nat.add_assoc p q r)).hom =
    (α_ ((linearHomCochainComplex R K₁ M₁).X p)
      ((linearHomCochainComplex R K₂ M₂).X q)
      ((linearHomCochainComplex R K₃ M₃).X r)).hom ≫
      (𝟙 ((linearHomCochainComplex R K₁ M₁).X p) ⊗ₘ
        (linearHomCochainGradedPairing R Δ₂₃ μ₂₃).pair q r) ≫
      (linearHomCochainGradedPairing R Δᵣ μᵣ).pair p (q + r) := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro φ ψ χ
  change (K₁.X p ⟶ M₁) at φ
  change (K₂.X q ⟶ M₂) at ψ
  change (K₃.X r ⟶ M₃) at χ
  change ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) Mᵣ).obj
      (op Kᵣ)).XIsoOfEq (Nat.add_assoc p q r)).hom).hom
        (((linearHomCochainComparison R c a).f ((p + q) + r)).hom
          (((linearHomCochainGradedPairing R Δₗ μₗ).pair (p + q) r).hom
            ((((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q).hom
              (φ ⊗ₜ[R] ψ)) ⊗ₜ[R] χ))) =
    ((linearHomCochainGradedPairing R Δᵣ μᵣ).pair p (q + r)).hom
      (φ ⊗ₜ[R] (((linearHomCochainGradedPairing R Δ₂₃ μ₂₃).pair q r).hom
        (ψ ⊗ₜ[R] χ)))
  erw [linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul,
    linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul,
    linearHomCochainComplex_XIsoOfEq_hom_apply',
    linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul,
    linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul]
  change (Kᵣ.XIsoOfEq (Nat.add_assoc p q r).symm).hom ≫
      c.f ((p + q) + r) ≫ Δₗ.f ((p + q) + r) ≫
        linearHomPairingDesc R μₗ (p + q) r
          (Δ₁₂.f (p + q) ≫ linearHomPairingDesc R μ₁₂ p q φ ψ) χ ≫ a =
    Δᵣ.f (p + (q + r)) ≫ linearHomPairingDesc R μᵣ p (q + r) φ
      (Δ₂₃.f (q + r) ≫ linearHomPairingDesc R μ₂₃ q r ψ χ)
  change (Kᵣ.XIsoOfEq (Nat.add_assoc p q r).symm).hom ≫
      (c ≫ Δₗ).f ((p + q) + r) ≫
        linearHomPairingDesc R μₗ (p + q) r
          (Δ₁₂.f (p + q) ≫ linearHomPairingDesc R μ₁₂ p q φ ψ) χ ≫ a = _
  rw [XIsoOfEq_comp_heterogeneousLinearHomPairingDesc_assoc R
    (c ≫ Δₗ) μₗ (p + q) r (p + (q + r))
    (Nat.add_assoc p q r).symm
    (Δ₁₂.f (p + q) ≫ linearHomPairingDesc R μ₁₂ p q φ ψ) χ]
  have hleftNat := heterogeneousLinearHomPairingDescOfEq_naturality
    (R := R) Δ₁₂ (𝟙 K₃) μₗ (p + q) r (p + (q + r))
    (Nat.add_assoc p q r)
    (linearHomPairingDesc R μ₁₂ p q φ ψ) χ
  simp only [id_f, Category.id_comp] at hleftNat
  have hrightNat := heterogeneousLinearHomPairingDescOfEq_naturality
    (R := R) (𝟙 K₁) Δ₂₃ μᵣ p (q + r) (p + (q + r)) rfl φ
    (linearHomPairingDesc R μ₂₃ q r ψ χ)
  simp only [id_f, Category.id_comp] at hrightNat
  rw [← hleftNat]
  rw [linearHomPairingDesc_eq_heterogeneous R μᵣ p (q + r) φ
    (Δ₂₃.f (q + r) ≫ linearHomPairingDesc R μ₂₃ q r ψ χ)]
  erw [← hrightNat]
  simp only [Category.assoc]
  rw [← heterogeneousLinearHomPairingDesc_assoc R μ₁₂ μₗ μ₂₃ μᵣ a hμ
    p q r (p + (q + r)) (Nat.add_assoc p q r) rfl φ ψ χ]
  have hΔn := congrArg (fun f => f.f (p + (q + r))) hΔ
  dsimp only [HomologicalComplex.comp_f] at hΔn
  change c.f (p + (q + r)) ≫ Δₗ.f (p + (q + r)) ≫
      (tensorHom Δ₁₂ (𝟙 K₃)).f (p + (q + r)) ≫
        (HomologicalComplex.associator K₁ K₂ K₃).hom.f (p + (q + r)) =
    Δᵣ.f (p + (q + r)) ≫
      (tensorHom (𝟙 K₁) Δ₂₃).f (p + (q + r)) at hΔn
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun f => f ≫
      heterogeneousLinearHomPairingDescOfEq R μᵣ p (q + r) (p + (q + r))
        rfl φ (linearHomPairingDesc R μ₂₃ q r ψ χ)) hΔn


theorem linearHomCochainPair_left_unit_of_diagrams
    {Kᵤ K Kₗ : ChainComplex (ModuleCat.{u} R) ℕ}
    {U M L : ModuleCat.{u} R}
    (Δ : Kₗ ⟶ Kᵤ ⊗ K)
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (c : K ⟶ Kₗ)
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U) (μ : U ⊗ M ⟶ L) (a : L ⟶ M)
    (hΔ : c ≫ Δ ≫ (ε ▷ K) ≫ (λ_ K).hom = 𝟙 K)
    (hμ : (e ▷ M) ≫ μ ≫ a = (λ_ M).hom)
    (q : ℕ) :
    (linearHomCochainUnitOfCounitHom R Kᵤ ε U e ▷
        (linearHomCochainComplex R K M).X q) ≫
      (linearHomCochainGradedPairing R Δ μ).pair 0 q ≫
      (linearHomCochainComparison R c a).f (0 + q) ≫
      ((linearHomCochainComplex R K M).XIsoOfEq (Nat.zero_add q)).hom =
    (λ_ ((linearHomCochainComplex R K M).X q)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r φ
  change R at r
  change (((linearHomCochainComplex R K M).XIsoOfEq
      (Nat.zero_add q)).hom).hom
        (((linearHomCochainComparison R c a).f (0 + q)).hom
          (((linearHomCochainGradedPairing R Δ μ).pair 0 q).hom
            ((r • linearHomCochainUnitOfCounit R Kᵤ ε U e) ⊗ₜ[R] φ))) =
    r • φ
  rw [← TensorProduct.smul_tmul']
  rw [map_smul, map_smul, map_smul]
  rw [linearHomCochainPair_left_unit_apply R Δ ε c e μ a hΔ hμ q φ]


theorem linearHomCochainPair_right_unit_of_diagrams
    {K Kᵤ Kₗ : ChainComplex (ModuleCat.{u} R) ℕ}
    {M U L : ModuleCat.{u} R}
    (Δ : Kₗ ⟶ K ⊗ Kᵤ)
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (c : K ⟶ Kₗ)
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U) (μ : M ⊗ U ⟶ L) (a : L ⟶ M)
    (hΔ : c ≫ Δ ≫ (K ◁ ε) ≫ (ρ_ K).hom = 𝟙 K)
    (hμ : (M ◁ e) ≫ μ ≫ a = (ρ_ M).hom)
    (p : ℕ) :
    ((linearHomCochainComplex R K M).X p ◁
        linearHomCochainUnitOfCounitHom R Kᵤ ε U e) ≫
      (linearHomCochainGradedPairing R Δ μ).pair p 0 ≫
      (linearHomCochainComparison R c a).f (p + 0) ≫
      ((linearHomCochainComplex R K M).XIsoOfEq (Nat.add_zero p)).hom =
    (ρ_ ((linearHomCochainComplex R K M).X p)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ r
  change R at r
  change (((linearHomCochainComplex R K M).XIsoOfEq
      (Nat.add_zero p)).hom).hom
        (((linearHomCochainComparison R c a).f (p + 0)).hom
          (((linearHomCochainGradedPairing R Δ μ).pair p 0).hom
            (φ ⊗ₜ[R] (r • linearHomCochainUnitOfCounit R Kᵤ ε U e)))) =
    r • φ
  rw [TensorProduct.tmul_smul]
  rw [map_smul, map_smul, map_smul]
  rw [linearHomCochainPair_right_unit_apply R Δ ε c e μ a hΔ hμ p φ]


end HomologicalComplex
