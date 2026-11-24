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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StagePushoutGeneral
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeak
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# The named general Waldhausen value on finite stages

The original genuine stage cofibrations and pointwise weak equivalences,
their actual algebra, the constructed zero stage and the whole general
stage pushout fill the original Waldhausen fields. Both zero and Waldhausen
values are named; no global instance or caller stage witness is used.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- An actual zero stage in every degree, from the existing canonical
zero diagram and its already proved finite-stage property. -/
noncomputable def generalStageZero (n : ℕ) : Stage C n :=
  ⟨zeroDiagram C n, isStage_zeroDiagram C n⟩


/-- The named original general-stage zero object's underlying diagram is the canonical constant
zero. -/
theorem generalStageZero_obj (n : ℕ) :
    (generalStageZero C n).obj = zeroDiagram C n := by
  unfold generalStageZero
  rfl

private theorem generalStageZero_isZero_aux (n : ℕ) :
    IsZero (generalStageZero C n) := by
  unfold generalStageZero
  apply IsZero.of_full_of_faithful_of_isZero (forget C n)
  change IsZero (zeroDiagram C n)
  exact Functor.isZero _ (fun _ => isZero_zero C)

/-- The actual canonical zero diagram is zero in the full stage category. -/
theorem generalStageZero_isZero (n : ℕ) : IsZero (generalStageZero C n) :=
  generalStageZero_isZero_aux C n

/-- Named stage zero-object data derived from the original zero diagram,
without an outer zero-object hypothesis or global instance. -/
theorem generalStageHasZeroObject (n : ℕ) : HasZeroObject (Stage C n) :=
  (generalStageZero_isZero C n).hasZeroObject

/-- Every original Waldhausen field on finite stages, using the genuine
stage cofibrations and the same original pointwise weak equivalences. -/
@[expose, instance_reducible]
noncomputable def generalStageWaldhausenCategory (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n;
    WaldhausenCategoryWithoutGluing (Stage C n) := by
  letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  exact {
    cofibrations := stageCofibrations C n
    weakEquivalences := stageWeak C n
    cofibrations_isMultiplicative := stageCofibrationsMultiplicative C n
    cofibrations_respectsIso := stageCofibrationsRespectsIso C n
    weakEquivalences_isMultiplicative := inferInstance
    weakEquivalences_respectsIso := inferInstance
    zero_isCofibration := fun X f =>
      stageCofibrations_of_isZero_source C n f (isZero_zero (Stage C n))
    cofibration_pushout := fun {X Y} i hi Z g => by
      let P := GeneralStagePushoutPresentation.ofStageCofibration (C := C) i g hi
      exact ⟨P.apex, P.inl, P.inr, P.isPushout, P.inlCofibration⟩ }

private theorem generalStageWaldhausenCategory_cofibration_aux (n : ℕ)
    {A B : Stage C n} (φ : A ⟶ B) :
    (letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n;
      letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n;
      IsCofibration φ) ↔ stageCofibrations C n φ := by
  unfold generalStageWaldhausenCategory
  rfl

/-- Cofibrations in the named stage value are exactly the original
successive-corner stage cofibrations used by its whole pushout constructor. -/
theorem isCofibration_generalStageWaldhausenCategory_iff (n : ℕ)
    {A B : Stage C n} (φ : A ⟶ B) :
    (letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n;
      letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n;
      IsCofibration φ) ↔ stageCofibrations C n φ :=
  generalStageWaldhausenCategory_cofibration_aux C n φ

private theorem generalStageWaldhausenCategory_weak_aux (n : ℕ)
    {A B : Stage C n} (φ : A ⟶ B) :
    (letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n;
      letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n;
      IsWeakEquivalence φ) ↔ stageWeak C n φ := by
  unfold generalStageWaldhausenCategory
  rfl

/-- Weak equivalences in the named stage value are exactly the same
original pointwise weak equivalences. -/
theorem isWeakEquivalence_generalStageWaldhausenCategory_iff (n : ℕ)
    {A B : Stage C n} (φ : A ⟶ B) :
    (letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n;
      letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n;
      IsWeakEquivalence φ) ↔ stageWeak C n φ :=
  generalStageWaldhausenCategory_weak_aux C n φ

end CategoryTheory.Waldhausen.SConstruction
