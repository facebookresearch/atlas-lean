/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofiberTripleEvaluation

/-!
# Original triple, diagonal, genuine corner and cocone clients
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial ZeroObject

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.StageCofiberTripleEvaluation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original triple evaluation preserves arbitrary original zero stages. -/
private theorem arbitraryZero (n : ℕ)
    {a b c : Fin (n + 1)} (hij : a ≤ b) (hjk : b ≤ c) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    ∀ {A : Stage C n} (_hA : IsZero A),
      IsZero ((stageCofiberTripleEvaluation C n hij hjk).obj A) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  intro A hA
  exact (stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk).map_isZero hA

/-- The mapped original stage zero has its actual relative selected-zero chart. -/
private def selectedZeroChart (n : ℕ)
    {a b c : Fin (n + 1)} (hij : a ≤ b) (hjk : b ≤ c) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    (stageCofiberTripleEvaluation C n hij hjk).obj (0 : Stage C n) ≅
      (0 : CofiberSequenceCategory C) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  exact ((stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk).map_isZero
    (isZero_zero _)).isoZero

/-- A genuine original stage map supplies the actual relative cofiber corner. -/
private theorem genuineRelativeCorner (n : ℕ)
    {a b c : Fin (n + 1)} (hij : a ≤ b) (hjk : b ≤ c) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    ∀ {A B : Stage C n} (φ : A ⟶ B) (_hφ : stageCofibrations C n φ),
      CofiberSequenceCategory.relativeCofibrations C
        ((stageCofiberTripleEvaluation C n hij hjk).map φ) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  intro A B φ hφ
  exact (CofiberSequenceCategory.isCofibration_relativeWaldhausenCategory_iff C _).mp
    ((stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk).map_cofibration φ
      ((isCofibration_generalStageWaldhausenCategory_iff C n φ).mpr hφ))

/-- The same original weak stage map gives the original relative weak map. -/
private theorem originalWeakMap (n : ℕ)
    {a b c : Fin (n + 1)} (hij : a ≤ b) (hjk : b ≤ c) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    ∀ {A B : Stage C n} (φ : A ⟶ B) (_hφ : stageWeak C n φ),
      IsWeakEquivalence ((stageCofiberTripleEvaluation C n hij hjk).map φ) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  intro A B φ hφ
  exact (stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk).map_weakEquivalence φ
    ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n φ).mpr hφ)

/-- Every supplied original stage pushout retains its mapped original apex and all legs. -/
private theorem everyGivenPushout (n : ℕ)
    {a b c : Fin (n + 1)} (hij : a ≤ b) (hjk : b ≤ c) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    ∀ {A B A' Q : Stage C n} (i : A ⟶ B) (f : A ⟶ A') (l : A' ⟶ Q) (r : B ⟶ Q)
      (_hi : stageCofibrations C n i) (_hQ : IsPushout f i l r),
      IsPushout ((stageCofiberTripleEvaluation C n hij hjk).map f)
        ((stageCofiberTripleEvaluation C n hij hjk).map i)
        ((stageCofiberTripleEvaluation C n hij hjk).map l)
        ((stageCofiberTripleEvaluation C n hij hjk).map r) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  intro A B A' Q i f l r hi hQ
  exact (stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk).map_pushout
    i f l r ((isCofibration_generalStageWaldhausenCategory_iff C n i).mpr hi) hQ

/-- The whole original stage cofiber row retains its mapped quotient arrow and apex. -/
private theorem wholeCofiberRow (n : ℕ)
    {a b c : Fin (n + 1)} (hij : a ≤ b) (hjk : b ≤ c) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    ∀ {A B Q : Stage C n} (i : A ⟶ B) (p : B ⟶ Q)
      (_hSeq : IsCofibrationSequence i p),
      IsCofibrationSequence ((stageCofiberTripleEvaluation C n hij hjk).map i)
        ((stageCofiberTripleEvaluation C n hij hjk).map p) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  intro A B Q i p hSeq
  exact (stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk).map_cofibrationSequence
    hSeq

/-- A repeated first endpoint retains the given original diagonal zero object. -/
private theorem repeatedFirstEndpoint (n : ℕ) {i k : Fin (n + 1)}
    (hik : i ≤ k) (A : Stage C n) :
    IsZero (((stageCofiberTripleEvaluation C n (le_refl i) hik).obj A).obj.obj' 0) := by
  change IsZero (A.obj.obj (diag i))
  exact A.property.diag_isZero i

/-- Both original inclusion and quotient arrows are the original interval-diagram maps. -/
private theorem originalArrows (n : ℕ) {i j k : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) (A : Stage C n) :
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.map' 0 1 =
      A.obj.map (horiz hij hjk) ∧
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.map' 1 2 =
      A.obj.map (vert hij hjk) :=
  ⟨stageCofiberTripleEvaluation_firstArrow C n hij hjk A,
    stageCofiberTripleEvaluation_secondArrow C n hij hjk A⟩

/-- The original reindex operator retains the complete same triple functor. -/
private theorem originalReindex {a b : SimplexCategory} (α : a ⟶ b)
    {i j k : Fin (a.len + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    reindexStage (C := C) α ⋙ stageCofiberTripleEvaluation C a.len hij hjk =
      stageCofiberTripleEvaluation C b.len
        (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk) :=
  stageCofiberTripleEvaluation_reindex C α hij hjk

#print axioms CategoryTheory.Waldhausen.SConstruction.stageTwoExtraction_isWaldhausenExact
#print axioms
  CategoryTheory.Waldhausen.SConstruction.stageCofiberTripleEvaluation_isWaldhausenExact

end MathlibExtTest.KTheory.Waldhausen.StageCofiberTripleEvaluation

end

