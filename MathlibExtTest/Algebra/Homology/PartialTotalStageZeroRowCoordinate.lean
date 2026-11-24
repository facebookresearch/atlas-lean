/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalStageZeroRowCoordinate

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.Abelian.SpectralObject

universe v u

namespace MathlibExtTest.Algebra.Homology.PartialTotalStageZeroRowCoordinate

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (q : ℕ) :=
  B.partialTotalStageZeroSourceCoordinate q

example (q : ℕ) :=
  B.partialTotalStageZeroSourceCoordinate_stageIso_heq q

example (q : ℕ) :=
  B.partialTotalStageZeroSourceIso q

example (q : ℕ) :
    (B.partialTotalStageZeroSourceIso q).hom = eqToHom (by
      simp only [
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
      rw [show -(q : ℤ) = -(0 : ℤ) - (q : ℤ) by omega]
      simp only [Int.cast_ofNat_Int, Int.neg_zero]
      congr 1) :=
  B.partialTotalStageZeroSourceIso_hom_eqToHom q

example (q : ℕ) :=
  B.partialTotalStageZeroSourceIso_homology_compatibility q

example : B.X 0 ⟶ B.partialTotal 0 :=
  B.partialTotalZeroRowToPartialTotal

example (q : ℕ) :
    (B.partialTotalZeroRowToPartialTotal).f q =
      (B.partialTotalLastRowIso 0).inv.f q ≫
        (B.firstStupidTrunc 0).ιTotal
          (ComplexShape.down ℕ) 0 q q (Nat.zero_add q) := by
  rfl

example :
    (B.partialTotalZeroRowToPartialTotal).f 0 =
      (B.partialTotalLastRowIso 0).inv.f 0 ≫
        (B.firstStupidTrunc 0).ιTotal
          (ComplexShape.down ℕ) 0 0 0 rfl := by
  rfl

example :
    (B.partialTotalZeroRowToPartialTotal).f 1 =
      (B.partialTotalLastRowIso 0).inv.f 1 ≫
        (B.firstStupidTrunc 0).ιTotal
          (ComplexShape.down ℕ) 0 1 1 rfl := by
  rfl

example (q : ℕ) :
    ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ⟶
      B.partialTotalFirstPageChoice.pageOne.X (0, q) :=
  B.partialTotalSpectralStepZeroToFirstPage q

example :
    ((B.partialTotalSpectralObject.H (0 : ℤ)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ⟶
      B.partialTotalFirstPageChoice.pageOne.X (0, 0) :=
  B.partialTotalSpectralStepZeroToFirstPage 0

example :
    ((B.partialTotalSpectralObject.H (-1 : ℤ)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ⟶
      B.partialTotalFirstPageChoice.pageOne.X (0, 1) :=
  B.partialTotalSpectralStepZeroToFirstPage 1

example (q : ℕ) :
    ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
      (mk₁ (homOfLE
        (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
    ((B.partialTotalSpectralObject.H ((core).deg (0, q))).obj
      (mk₁ (homOfLE ((core).le₁₂ (0, q))))) :=
  B.partialTotalSpectralStepZeroCoreIso q

example :
    ((B.partialTotalSpectralObject.H (0 : ℤ)).obj
      (mk₁ (homOfLE
        (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
    ((B.partialTotalSpectralObject.H ((core).deg (0, 0))).obj
      (mk₁ (homOfLE ((core).le₁₂ (0, 0))))) :=
  B.partialTotalSpectralStepZeroCoreIso 0

example :
    ((B.partialTotalSpectralObject.H (-1 : ℤ)).obj
      (mk₁ (homOfLE
        (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
    ((B.partialTotalSpectralObject.H ((core).deg (0, 1))).obj
      (mk₁ (homOfLE ((core).le₁₂ (0, 1))))) :=
  B.partialTotalSpectralStepZeroCoreIso 1

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
example (q : ℕ) :
    B.partialTotalSpectralStepZeroToFirstPage q =
      (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
        (B.partialTotalFirstPageChoice.firstPageCoreIsoAt 0 q).inv := by
  rfl

example (q : ℕ) :=
  B.partialTotalSpectralStepZeroCoreIso_hom q

example (q : ℕ) :
    HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal q ≫
        (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
        B.partialTotalSpectralStepZeroToFirstPage q =
      (B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)).inv ≫
        (B.partialTotalFirstPageChoice.firstPageRowIsoAt
          0 q q (Nat.zero_add q)).inv :=
  B.partialTotalZeroRowToPartialTotal_homologyMap_comp_stepZeroToFirstPage q

example :
    HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal 0 ≫
        (B.partialTotalSpectralStepHomologyIso 0 0).inv ≫
        B.partialTotalSpectralStepZeroToFirstPage 0 =
      (B.totalRowHomologyIsoAt 0 0 0 rfl).inv ≫
        (B.partialTotalFirstPageChoice.firstPageRowIsoAt 0 0 0 rfl).inv :=
  B.partialTotalZeroRowToPartialTotal_homologyMap_comp_stepZeroToFirstPage 0

example :
    HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal 1 ≫
        (B.partialTotalSpectralStepHomologyIso 1 0).inv ≫
        B.partialTotalSpectralStepZeroToFirstPage 1 =
      (B.totalRowHomologyIsoAt 0 1 1 rfl).inv ≫
        (B.partialTotalFirstPageChoice.firstPageRowIsoAt 0 1 1 rfl).inv :=
  B.partialTotalZeroRowToPartialTotal_homologyMap_comp_stepZeroToFirstPage 1

local notation "B₀" =>
  (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example : (B₀).X 0 ⟶ HomologicalComplex₂.partialTotal B₀ 0 :=
  HomologicalComplex₂.partialTotalZeroRowToPartialTotal B₀

example (q : ℕ) :
    (((HomologicalComplex₂.partialTotalSpectralObject B₀).H (-(q : ℤ))).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ⟶
      (HomologicalComplex₂.partialTotalFirstPageChoice B₀).pageOne.X (0, q) :=
  HomologicalComplex₂.partialTotalSpectralStepZeroToFirstPage B₀ q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroRowToPartialTotal_homologyMap_comp_stepZeroToFirstPage
    B₀ q

end MathlibExtTest.Algebra.Homology.PartialTotalStageZeroRowCoordinate

end
