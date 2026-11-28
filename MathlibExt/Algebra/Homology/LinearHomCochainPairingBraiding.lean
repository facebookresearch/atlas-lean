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

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}
variable [HasTensor K L] [HasTensor L K]
variable {M N P : ModuleCat.{u} R}

private theorem linearHomPairingDesc_koszul_braiding
    (μ : M ⊗ N ⟶ P) (μ' : N ⊗ M ⟶ P)
    (hμ : (β_ M N).hom ≫ μ' = μ)
    (p q : ℕ) (φ : K.X p ⟶ M) (ψ : L.X q ⟶ N) :
    (koszulTensorBraidingIso K L).hom.f (p + q) ≫
        ((tensorObj L K).XIsoOfEq (Nat.add_comm p q)).hom ≫
        linearHomPairingDesc R μ' q p ψ φ =
      ((-1 : ℤ) ^ (p * q)) • linearHomPairingDesc R μ p q φ ψ := by
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = p + q at hij
  change ιTensorObj K L i j (p + q) hij ≫
      (koszulTensorBraidingIso K L).hom.f (p + q) ≫
        ((tensorObj L K).XIsoOfEq (Nat.add_comm p q)).hom ≫
          linearHomPairingDesc R μ' q p ψ φ =
    ιTensorObj K L i j (p + q) hij ≫
      (((-1 : ℤ) ^ (p * q)) • linearHomPairingDesc R μ p q φ ψ)
  rw [ιTensorObj_koszulTensorBraidingIso_hom_assoc]
  rw [Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [ιTensorObj_comp_XIsoOfEq_assoc]
  rw [Preadditive.comp_zsmul]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel hij
    subst j
    rw [ιTensorObj_comp_linearHomPairingDesc
      (R := R) (K₁ := L) (K₂ := K) μ' q p q p]
    rw [ιTensorObj_comp_linearHomPairingDesc
      (R := R) (K₁ := K) (K₂ := L) μ p q p q]
    simp only [dite_eq_left, ComplexShape.σ_down_ℕ]
    change ((-1 : ℤ) ^ (p * q)) •
        ((β_ (K.X p) (L.X q)).hom ≫ (ψ ⊗ₘ φ) ≫ μ') =
      ((-1 : ℤ) ^ (p * q)) • ((φ ⊗ₘ ψ) ≫ μ)
    rw [← BraidedCategory.braiding_naturality_assoc, hμ]
  · have hj : j ≠ q := by
      intro hj
      subst j
      exact hi (Nat.add_right_cancel hij)
    rw [ιTensorObj_comp_linearHomPairingDesc
      (R := R) (K₁ := L) (K₂ := K) μ' q p j i]
    rw [ιTensorObj_comp_linearHomPairingDesc
      (R := R) (K₁ := K) (K₂ := L) μ p q i j]
    simp [hi, hj]

@[simp]
private lemma moduleHom_comp_apply {A B C : ModuleCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[simp]
private lemma moduleHom_zsmul_apply {A B : ModuleCat.{u} R}
    (z : ℤ) (f : A ⟶ B) (x : A) :
    (z • f).hom x = z • f.hom x := rfl

@[simp]
private lemma linearHomCochainComplex_XIsoOfEq_hom_apply'
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (G : ModuleCat.{u} R)
    {a b : ℕ} (h : a = b) (φ : K.X a ⟶ G) :
    ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) G).obj
      (Opposite.op K)).XIsoOfEq h).hom).hom φ =
      (K.XIsoOfEq h.symm).hom ≫ φ := by
  subst b
  rfl

/-- Let R be a commutative ring, K, L, K₃ nonnegative chain complexes of
R-modules, and Δ : K₃ → K ⊗ L a chain map, with both K ⊗ L and L ⊗ K
defined. Let μ : M ⊗[R] N → P and μ′ : N ⊗[R] M → P satisfy
μ′ ∘ β_(M,N) = μ. For p, q ∈ ℕ, interchange the input Hom cochains,
use the diagonal β_(K,L) ∘ Δ and μ′, and identify q + p with p + q
in the output cochain complex. The resulting pairing equals
(-1)^(p*q) times the pairing from Δ and μ. -/
theorem linearHomCochainPair_koszul_swap
    {Κ Λ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    [HasTensor Κ Λ] [HasTensor Λ Κ]
    (Δ : K₃ ⟶ tensorObj Κ Λ)
    (μ : M ⊗ N ⟶ P) (μ' : N ⊗ M ⟶ P)
    (hμ : (β_ M N).hom ≫ μ' = μ)
    (p q : ℕ) :
    (β_
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (Opposite.op Κ)).X p)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj
          (Opposite.op Λ)).X q)).hom ≫
      (linearHomCochainGradedPairing R
        (Δ ≫ (koszulTensorBraidingIso Κ Λ).hom) μ').pair q p ≫
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).obj
        (Opposite.op K₃)).XIsoOfEq (Nat.add_comm q p)).hom =
      ((-1 : ℤ) ^ (p * q)) •
        (linearHomCochainGradedPairing R Δ μ).pair p q := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ ψ
  simp only [moduleHom_comp_apply, moduleHom_zsmul_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]
  change (Κ.X p ⟶ M) at φ
  change (Λ.X q ⟶ N) at ψ
  erw [linearHomCochainGradedPairing_pair,
    linearHomCochainPair_tmul,
    linearHomCochainComplex_XIsoOfEq_hom_apply',
    linearHomCochainGradedPairing_pair,
    linearHomCochainPair_tmul]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [← XIsoOfEq_hom_naturality_assoc Δ (Nat.add_comm p q)]
  rw [← XIsoOfEq_hom_naturality_assoc
    (koszulTensorBraidingIso Κ Λ).hom (Nat.add_comm p q)]
  rw [linearHomPairingDesc_koszul_braiding R μ μ' hμ p q φ ψ]
  rw [Preadditive.comp_zsmul]
  rfl

end HomologicalComplex
