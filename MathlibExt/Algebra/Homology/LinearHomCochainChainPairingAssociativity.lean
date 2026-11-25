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

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.CochainChainGradedPairingHomology
public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing
@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace HomologicalComplex.CochainChainGradedPairing

variable (R : Type u) [CommRing R]

/-- Evaluate a cochain-chain homology pairing on classes represented by cycles. -/
@[simp]
lemma pairHomology_π_apply
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    (x : K.cycles p) (y : L.cycles (p + q)) :
    (P.pairHomology p q).hom
        ((K.homologyπ p).hom x ⊗ₜ[R] (L.homologyπ (p + q)).hom y) =
      (M.homologyπ q).hom ((P.pairCycles p q).hom (x ⊗ₜ[R] y)) := by
  exact ConcreteCategory.congr_hom
    (tensor_homologyπ_comp_pairHomology P p q) (x ⊗ₜ[R] y)

/-- A heterogeneous cup-cap associativity identity on cycles descends to homology. -/
theorem pairHomology_associativity
    {K₁ K₂ K₁₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M₂₃ Mₗ Mᵣ : ChainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainChainGradedPairing K₁₂ L Mₗ)
    (P₂₃ : CochainChainGradedPairing K₂ L M₂₃)
    (Pᵣ : CochainChainGradedPairing K₁ M₂₃ Mᵣ)
    (p q r : ℕ)
    (inputCycles : L.cycles ((p + q) + r) ⟶ L.cycles (q + (p + r)))
    (input : L.homology ((p + q) + r) ⟶ L.homology (q + (p + r)))
    (comparison : Mₗ.homology r ⟶ Mᵣ.homology r)
    (input_π : L.homologyπ ((p + q) + r) ≫ input =
      inputCycles ≫ L.homologyπ (q + (p + r)))
    (hcycles :
      (P₁₂.pairCycles p q ⊗ₘ 𝟙 (L.cycles ((p + q) + r))) ≫
          Pₗ.pairCycles (p + q) r ≫ Mₗ.homologyπ r ≫ comparison =
        (α_ (K₁.cycles p) (K₂.cycles q)
          (L.cycles ((p + q) + r))).hom ≫
          (𝟙 (K₁.cycles p) ⊗ₘ
            ((𝟙 (K₂.cycles q) ⊗ₘ inputCycles) ≫
              P₂₃.pairCycles q (p + r))) ≫
          Pᵣ.pairCycles p r ≫ Mᵣ.homologyπ r) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (L.homology ((p + q) + r))) ≫
        Pₗ.pairHomology (p + q) r ≫ comparison =
      (α_ (K₁.homology p) (K₂.homology q)
        (L.homology ((p + q) + r))).hom ≫
        (𝟙 (K₁.homology p) ⊗ₘ
          ((𝟙 (K₂.homology q) ⊗ₘ input) ≫
            P₂₃.pairHomology q (p + r))) ≫
        Pᵣ.pairHomology p r := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  obtain ⟨x₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₁.homologyπ p)).mp inferInstance x
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₂.homologyπ q)).mp inferInstance y
  obtain ⟨z₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective
      (L.homologyπ ((p + q) + r))).mp inferInstance z
  change comparison.hom
      ((Pₗ.pairHomology (p + q) r).hom
        ((P₁₂.pairHomology p q).hom
            ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
              (K₂.homologyπ q).hom y₀) ⊗ₜ[R]
          (L.homologyπ ((p + q) + r)).hom z₀)) =
    (Pᵣ.pairHomology p r).hom
      ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
        (P₂₃.pairHomology q (p + r)).hom
          ((K₂.homologyπ q).hom y₀ ⊗ₜ[R]
            input.hom ((L.homologyπ ((p + q) + r)).hom z₀)))
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply R P₁₂,
    pairHomology_π_apply R Pₗ]
  have hinput := ConcreteCategory.congr_hom input_π z₀
  change input.hom ((L.homologyπ ((p + q) + r)).hom z₀) =
    (L.homologyπ (q + (p + r))).hom (inputCycles.hom z₀) at hinput
  rw [hinput, pairHomology_π_apply R P₂₃, pairHomology_π_apply R Pᵣ]
  exact ConcreteCategory.congr_hom hcycles
    ((x₀ ⊗ₜ[R] y₀) ⊗ₜ[R] z₀)

/-- An underlying cup-cap identity descends through explicit input and output comparisons. -/
theorem pairHomology_associativity_of_pair
    {K₁ K₂ K₁₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M₂₃ Mₗ Mᵣ : ChainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainChainGradedPairing K₁₂ L Mₗ)
    (P₂₃ : CochainChainGradedPairing K₂ L M₂₃)
    (Pᵣ : CochainChainGradedPairing K₁ M₂₃ Mᵣ)
    (p q r : ℕ)
    (inputX : L.X ((p + q) + r) ⟶ L.X (q + (p + r)))
    (inputCycles : L.cycles ((p + q) + r) ⟶ L.cycles (q + (p + r)))
    (inputHomology : L.homology ((p + q) + r) ⟶
      L.homology (q + (p + r)))
    (outputX : Mₗ.X r ⟶ Mᵣ.X r)
    (outputCycles : Mₗ.cycles r ⟶ Mᵣ.cycles r)
    (outputHomology : Mₗ.homology r ⟶ Mᵣ.homology r)
    (inputCycles_i : inputCycles ≫ L.iCycles (q + (p + r)) =
      L.iCycles ((p + q) + r) ≫ inputX)
    (input_π : L.homologyπ ((p + q) + r) ≫ inputHomology =
      inputCycles ≫ L.homologyπ (q + (p + r)))
    (outputCycles_i : outputCycles ≫ Mᵣ.iCycles r =
      Mₗ.iCycles r ≫ outputX)
    (output_π : Mₗ.homologyπ r ≫ outputHomology =
      outputCycles ≫ Mᵣ.homologyπ r)
    (hpair :
      (P₁₂.pair p q ⊗ₘ 𝟙 (L.X ((p + q) + r))) ≫
          Pₗ.pair (p + q) r ≫ outputX =
        (α_ (K₁.X p) (K₂.X q) (L.X ((p + q) + r))).hom ≫
          (𝟙 (K₁.X p) ⊗ₘ
            ((𝟙 (K₂.X q) ⊗ₘ inputX) ≫
              P₂₃.pair q (p + r))) ≫
          Pᵣ.pair p r) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (L.homology ((p + q) + r))) ≫
        Pₗ.pairHomology (p + q) r ≫ outputHomology =
      (α_ (K₁.homology p) (K₂.homology q)
        (L.homology ((p + q) + r))).hom ≫
        (𝟙 (K₁.homology p) ⊗ₘ
          ((𝟙 (K₂.homology q) ⊗ₘ inputHomology) ≫
            P₂₃.pairHomology q (p + r))) ≫
        Pᵣ.pairHomology p r := by
  apply pairHomology_associativity R P₁₂ Pₗ P₂₃ Pᵣ p q r
    inputCycles inputHomology outputHomology input_π
  rw [output_π]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono (Mᵣ.iCycles r)).1
  have hrightInner :
      ((𝟙 (K₂.cycles q) ⊗ₘ inputCycles) ≫
          P₂₃.pairCycles q (p + r)) ≫ M₂₃.iCycles (p + r) =
        (K₂.iCycles q ⊗ₘ L.iCycles ((p + q) + r)) ≫
          (𝟙 (K₂.X q) ⊗ₘ inputX) ≫ P₂₃.pair q (p + r) := by
    rw [Category.assoc, P₂₃.pairCycles_i]
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
    rw [inputCycles_i]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    simp
  simp only [Category.assoc]
  rw [outputCycles_i, Pₗ.pairCycles_i_assoc, Pᵣ.pairCycles_i]
  slice_lhs 1 2 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  slice_rhs 2 3 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [P₁₂.pairCycles_i]
  simp only [Category.id_comp]
  rw [hrightInner]
  have hleftTensor :
      (((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P₁₂.pair p q) ⊗ₘ
          L.iCycles ((p + q) + r)) =
        ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ⊗ₘ
            L.iCycles ((p + q) + r)) ≫
          (P₁₂.pair p q ⊗ₘ 𝟙 (L.X ((p + q) + r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hrightTensor :
      (K₁.iCycles p ⊗ₘ
          ((K₂.iCycles q ⊗ₘ L.iCycles ((p + q) + r)) ≫
            (𝟙 (K₂.X q) ⊗ₘ inputX) ≫ P₂₃.pair q (p + r))) =
        (K₁.iCycles p ⊗ₘ
            (K₂.iCycles q ⊗ₘ L.iCycles ((p + q) + r))) ≫
          (𝟙 (K₁.X p) ⊗ₘ
            ((𝟙 (K₂.X q) ⊗ₘ inputX) ≫
              P₂₃.pair q (p + r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hleftTensor, hrightTensor]
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_naturality_assoc]
  rw [hpair]

end HomologicalComplex.CochainChainGradedPairing

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

noncomputable local instance mixedAssociativityMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- A componentwise diagram gives the mixed Linear-Hom cup--cap pairing
associativity identity needed before descending to homology. -/
public theorem linearHomCochainChainPair_associativity_of_diagrams
    {K₁ K₂ K₁₂ L Jₗ J₂₃ M₂₃ Jᵣ Mₗ Mᵣ :
      ChainComplex (ModuleCat.{u} R) ℕ}
    {A₁ A₂ A₁₂ : ModuleCat.{u} R}
    (Δ₁₂ : K₁₂ ⟶ K₁ ⊗ K₂) (Δₗ : L ⟶ K₁₂ ⊗ Jₗ)
    (Δ₂₃ : L ⟶ K₂ ⊗ J₂₃) (Δᵣ : M₂₃ ⟶ K₁ ⊗ Jᵣ)
    (μ₁₂ : A₁ ⊗ A₂ ⟶ A₁₂)
    (ρₗ : ∀ i, A₁₂ ⊗ Jₗ.X i ⟶ Mₗ.X i)
    (ρ₂₃ : ∀ i, A₂ ⊗ J₂₃.X i ⟶ M₂₃.X i)
    (ρᵣ : ∀ i, A₁ ⊗ Jᵣ.X i ⟶ Mᵣ.X i)
    (p q r : ℕ)
    (inputX : L.X ((p + q) + r) ⟶ L.X (q + (p + r)))
    (outputX : Mₗ.X r ⟶ Mᵣ.X r)
    (hdiagram : ∀ (φ : K₁.X p ⟶ A₁) (ψ : K₂.X q ⟶ A₂),
      Δₗ.f ((p + q) + r) ≫
          linearHomCochainChainPairDesc R ρₗ (p + q) r
            (Δ₁₂.f (p + q) ≫
              linearHomPairingDesc R μ₁₂ p q φ ψ) ≫
          outputX =
        inputX ≫ Δ₂₃.f (q + (p + r)) ≫
          linearHomCochainChainPairDesc R ρ₂₃ q (p + r) ψ ≫
          Δᵣ.f (p + r) ≫
          linearHomCochainChainPairDesc R ρᵣ p r φ) :
    ((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q ⊗ₘ
          𝟙 (L.X ((p + q) + r))) ≫
        linearHomCochainChainPair R Δₗ ρₗ (p + q) r ≫ outputX =
      (α_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
          (Opposite.op K₁)).X p)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
          (Opposite.op K₂)).X q)
        (L.X ((p + q) + r))).hom ≫
        (𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
            (Opposite.op K₁)).X p) ⊗ₘ
          ((𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
              (Opposite.op K₂)).X q) ⊗ₘ inputX) ≫
            linearHomCochainChainPair R Δ₂₃ ρ₂₃ q (p + r))) ≫
        linearHomCochainChainPair R Δᵣ ρᵣ p r := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro φ ψ x
  change outputX.hom
      ((linearHomCochainChainPair R Δₗ ρₗ (p + q) r).hom
        (((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q).hom
            (φ ⊗ₜ[R] ψ) ⊗ₜ[R] x)) =
    (linearHomCochainChainPair R Δᵣ ρᵣ p r).hom
      (φ ⊗ₜ[R]
        (linearHomCochainChainPair R Δ₂₃ ρ₂₃ q (p + r)).hom
          (ψ ⊗ₜ[R] inputX.hom x))
  erw [linearHomCochainGradedPairing_pair,
    linearHomCochainPair_tmul,
    linearHomCochainChainPair_tmul,
    linearHomCochainChainPair_tmul,
    linearHomCochainChainPair_tmul]
  exact ConcreteCategory.congr_hom (hdiagram φ ψ) x

end HomologicalComplex
end
