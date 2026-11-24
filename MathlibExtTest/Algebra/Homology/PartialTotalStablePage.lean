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

import MathlibExt.Algebra.Homology.PartialTotalStablePage

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat


example :
    IsZero ((B.partialTotalSpectralObject.H (-1)).obj
      (ComposableArrows.mk₁
        (homOfLE (show ((1 : ℤ) : EInt) ≤ ⊤ by simp)))) :=
  B.isZero_partialTotalSpectralObjectHObj_stage_to_top 1 0 (by omega)

example (k : ℕ) :
    IsZero ((B.partialTotalSpectralObject.H (-((k + 1 : ℕ) : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show (((k + 1 : ℕ) : ℤ) : EInt) ≤ ⊤ by simp)))) :=
  B.isZero_partialTotalSpectralObjectHObj_stage_to_top (k + 1) k le_rfl

example (s k : ℕ) (h : k + 1 ≤ s) :
    IsZero ((B.partialTotalSpectralObject.H (-((k + 1 : ℕ) : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show ((s : ℤ) : EInt) ≤ ⊤ by simp)))) :=
  B.isZero_partialTotalSpectralObjectHObj_stage_to_top s k h

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
        (((p + q + 2 : ℕ) : ℤ))).X (p, q) ≅
      B.partialTotalStableObj (p + q) p :=
  B.partialTotalStablePageIso p q

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
        (((p + q + 2 : ℕ) : ℤ))).X (p, q) ≅
      B.partialTotalHomologyGradedPiece (p + q) p :=
  B.partialTotalStablePageGradedIso p q

example (p q : ℕ) :
    (B.partialTotalHomologyFiltrationToStable (p + q) p ≫
        (B.partialTotalStablePageIso p q).inv) ≫
      (B.partialTotalStablePageGradedIso p q).hom =
    B.partialTotalHomologyGradedπ (p + q) p :=
  B.partialTotalHomologyFiltrationToStablePage_comp_gradingIso_hom p q

example :
    ((B.partialTotalSpectralObject.spectralSequence core).page 2).X (0, 0) ≅
      B.partialTotalHomologyGradedPiece 0 0 :=
  B.partialTotalStablePageGradedIso 0 0

example :
    ((B.partialTotalSpectralObject.spectralSequence core).page 3).X (0, 1) ≅
      B.partialTotalHomologyGradedPiece 1 0 :=
  B.partialTotalStablePageGradedIso 0 1

example :
    ((B.partialTotalSpectralObject.spectralSequence core).page 3).X (1, 0) ≅
      B.partialTotalHomologyGradedPiece 1 1 :=
  B.partialTotalStablePageGradedIso 1 0

example (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  B.partialTotalStablePageZeroColumnHom q

example :
    let f : (q : ℕ) →
        ((B.partialTotalSpectralObject.spectralSequence core).page
          (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
          B.partialTotalStableObj q 0 := fun q => by
      let Y := B.partialTotalSpectralObject
      let rD : ℤ := ((2 + q : ℕ) : ℤ)
      let rS : ℤ := ((0 + q + 2 : ℕ) : ℤ)
      have hrS : (1 : ℤ) ≤ rS := by
        dsimp only [rS]
        omega
      let i₀ : EInt := (((0 : ℤ) - rD : ℤ) : EInt)
      let i₁ : EInt := partialTotalHomologyPreviousIndex 0
      let i₂ : EInt := ((0 : ℤ) : EInt)
      let i₃ : EInt := (((0 : ℤ) + rD - 1 : ℤ) : EInt)
      let n₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
      let n₁ : ℤ := -(0 : ℤ) - (q : ℤ)
      let n₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
      have hn : n₁ = (core).deg (0, q) := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
            (0, q)).symm
      have hn₁ : n₀ + 1 = n₁ := by
        dsimp only [n₀, n₁]
        omega
      have hn₂ : n₁ + 1 = n₂ := by
        dsimp only [n₁, n₂]
      have hi₀ : i₀ = (core).i₀ rS (0, q) hrS := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
        dsimp only [i₀, rD, rS]
        congr 1
        omega
      have hi₁ : i₁ = (core).i₁ (0, q) := by
        change i₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
        dsimp only [i₁, partialTotalHomologyPreviousIndex]
        rfl
      have hi₂ : i₂ = (core).i₂ (0, q) := rfl
      have hi₃ : i₃ = (core).i₃ rS (0, q) hrS := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
        dsimp only [i₃, rD, rS]
        congr 1
        omega
      have hi₀neg : i₀ = ((-rD : ℤ) : EInt) := by
        dsimp only [i₀]
        congr 1
        omega
      have hi₀₁ : i₀ ≤ i₁ := by
        dsimp only [i₀, i₁, rD, partialTotalHomologyPreviousIndex]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₁₂ : i₁ ≤ i₂ := partialTotalHomologyPreviousIndex_le 0
      have hi₂₃ : i₂ ≤ i₃ := by
        dsimp only [i₂, i₃, rD]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
      have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
      have hLeft : IsZero ((Y.H n₂).obj
          (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
        rw [hi₀neg]
        exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
          n₂ (-rD) (by dsimp only [rD]; omega)
      let ePage := Y.spectralSequencePageXIso core rS hrS (0, q)
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
          (hn₁ := hn₁) (hn₂ := hn₂)
      let eLeft := Y.isoMapFourδ₁Toδ₀'
        (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
          n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
      let rightOuterMap := Y.mapFourδ₄Toδ₃'
        (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
          n₀ n₁ n₂ hn₁ hn₂
      have hTarget :
          Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
              (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ =
            B.partialTotalStableObj q 0 := by
        dsimp only [partialTotalStableObj,
          CategoryTheory.Abelian.SpectralObject.stableIntervalObj,
          CategoryTheory.Abelian.SpectralObject.stableIntervalLeft,
          CategoryTheory.Abelian.SpectralObject.stableIntervalMiddle,
          CategoryTheory.Abelian.SpectralObject.stableIntervalRight,
          n₀, n₁, n₂]
        congr 1
        all_goals omega
      exact ePage.hom ≫ eLeft.inv ≫ rightOuterMap ≫
        (eqToIso hTarget).hom
    (∀ q : ℕ, B.partialTotalStablePageZeroColumnHom q = f q) ∧
      B.partialTotalStablePageZeroColumnHom 0 = f 0 ∧
      B.partialTotalStablePageZeroColumnHom 1 = f 1 := by
  dsimp only
  constructor
  · intro q
    rfl
  · constructor <;> rfl

example (q : ℕ) :
    (B.partialTotalStablePageIso 0 q).hom ≫
        (eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
          (Nat.zero_add q))).hom =
      B.partialTotalStablePageZeroColumnHom q :=
  B.partialTotalStablePageIso_zero_hom_comp_eqToIso_hom q

example :
    (B.partialTotalStablePageIso 0 0).hom ≫
        (eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
          (Nat.zero_add 0))).hom =
      B.partialTotalStablePageZeroColumnHom 0 :=
  B.partialTotalStablePageIso_zero_hom_comp_eqToIso_hom 0

example :
    (B.partialTotalStablePageIso 0 1).hom ≫
        (eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
          (Nat.zero_add 1))).hom =
      B.partialTotalStablePageZeroColumnHom 1 :=
  B.partialTotalStablePageIso_zero_hom_comp_eqToIso_hom 1

end HomologicalComplex₂

end
