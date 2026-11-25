/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Actual R-coefficient classes of the original projective free module maps

The original finite-bijection free module comparison gives the actual residual
R coefficient, with its original complement-action orbit copower. Underlying
cofibrancy of each original R degree produces both original evaluated classes.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor I C) [MonObj R]

/-- The literal residual R-coefficient functor with its original orbit index. -/
abbrev coefficientCopower {n m : ℕ} (h : n ≤ m) : C ⥤ C :=
  tensorLeft (R.functor.obj (card (m - n))) ⋙ sigmaConst ⋙
    (CategoryTheory.evaluation (Type 0) C).obj (cardCosetIndex n m h)

/-- The whole original evaluated free R-module functor is its actual residual coefficient copower.
-/
def freeCoefficientIso {n m : ℕ} (h : n ≤ m) :
    CategoryTheory.Mod.dayFreeAt R (card n) ⋙ CategoryTheory.Mod.dayEvaluation R (card m) ≅
      coefficientCopower R h :=
  CategoryTheory.Mod.dayFreeAtCardInducedIso R h ≪≫ cardInducedCosetCopowerIso R h

omit [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] [MonObj R] in
/-- Each original coefficient summand retains the same original R object and base source. -/
theorem coefficientCopower_obj {n m : ℕ} (h : n ≤ m) (X : C) :
    (coefficientCopower R h).obj X = ∐ fun _ : cardCosetIndex n m h => R.functor.obj (card (m - n))
        ⊗ X := rfl

omit [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] [MonObj R] in
/-- Every actual coefficient summand retains the original tensor map. -/
theorem coefficientCopower_map {n m : ℕ} (h : n ≤ m) {X Y : C} (f : X ⟶ Y) :
    (coefficientCopower R h).map f =
      Limits.Sigma.map (fun _ : cardCosetIndex n m h => R.functor.obj (card (m - n)) ◁ f) := rfl

variable [ModelCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (card n)))

include hR in
/-- Genuinely cofibrant R degrees preserve every original evaluated free cofibration. -/
theorem projectiveFreeAt_evaluated_cofibration (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) :
    cofibrations C ((CategoryTheory.Mod.dayEvaluation R (card m)).map
      ((CategoryTheory.Mod.dayFreeAt R (card n)).map f)) := by
  by_cases h : n ≤ m
  · let _ : IsCofibrant (R.functor.obj (card (m - n))) := hR (m - n)
    let _ : (cofibrations C).IsStableUnderCoproducts.{0} :=
      IsStableUnderCoproducts.of_llp_eq _ _ (trivialFibrations_llp C)
    let q := cardCosetIndex n m h
    let τ : Discrete.functor (fun _ : q => R.functor.obj (card (m - n)) ⊗ X) ⟶
        Discrete.functor (fun _ : q => R.functor.obj (card (m - n)) ⊗ Y) :=
      Discrete.natTrans (fun _ => R.functor.obj (card (m - n)) ◁ f)
    have ht : cofibrations C ((coefficientCopower R h).map f) :=
      MorphismProperty.colimMap (W := cofibrations C) τ
        (fun _ => (ihomAdjunction_isQuillenAdjunction_of_isCofibrant _).preservesCofibrations f hf)
    exact ((cofibrations C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor C C).mapIso (freeCoefficientIso R h)).app (Arrow.mk f))).mpr ht
  · let e := CategoryTheory.Mod.dayFreeAtCardBelowIso R (Nat.lt_of_not_ge h)
    have hid : cofibrations C (𝟙 (⊥_ C)) := mem_cofibrations _
    exact ((cofibrations C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor C C).mapIso e).app (Arrow.mk f))).mpr hid

include hR in
/-- Genuinely cofibrant R degrees preserve every original evaluated free trivial cofibration. -/
theorem projectiveFreeAt_evaluated_trivialCofibration (n m : ℕ) {X Y : C} (f : X ⟶ Y)
    (hf : trivialCofibrations C f) :
    trivialCofibrations C ((CategoryTheory.Mod.dayEvaluation R (card m)).map
      ((CategoryTheory.Mod.dayFreeAt R (card n)).map f)) := by
  by_cases h : n ≤ m
  · let _ : IsCofibrant (R.functor.obj (card (m - n))) := hR (m - n)
    let _ : (trivialCofibrations C).IsStableUnderCoproducts.{0} :=
      IsStableUnderCoproducts.of_llp_eq _ _ (fibrations_llp C)
    let q := cardCosetIndex n m h
    let τ : Discrete.functor (fun _ : q => R.functor.obj (card (m - n)) ⊗ X) ⟶
        Discrete.functor (fun _ : q => R.functor.obj (card (m - n)) ⊗ Y) :=
      Discrete.natTrans (fun _ => R.functor.obj (card (m - n)) ◁ f)
    have ht : trivialCofibrations C ((coefficientCopower R h).map f) :=
      MorphismProperty.colimMap (W := trivialCofibrations C) τ
        (fun _ =>
            (ihomAdjunction_isQuillenAdjunction_of_isCofibrant _).preservesTrivialCofibrations f hf)
    exact ((trivialCofibrations C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor C C).mapIso (freeCoefficientIso R h)).app (Arrow.mk f))).mpr ht
  · let e := CategoryTheory.Mod.dayFreeAtCardBelowIso R (Nat.lt_of_not_ge h)
    have hid : trivialCofibrations C (𝟙 (⊥_ C)) := mem_trivialCofibrations _
    exact ((trivialCofibrations C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor C C).mapIso e).app (Arrow.mk f))).mpr hid

end HomotopicalAlgebra.PositiveLevelModel
