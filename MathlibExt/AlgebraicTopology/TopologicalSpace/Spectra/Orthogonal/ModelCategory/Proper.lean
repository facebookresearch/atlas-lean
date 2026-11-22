/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.ModelCategory.LevelCofibrations
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHProper
import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer.Proper

/-!
# Left properness of the actual orthogonal native level model

The model dictionary is the canonical native level model. Its original
free-I cell and retract proof gives coefficient cofibrations at every degree.
Actual enriched evaluations preserve the caller's pushout square. Left
properness of the same pointed CGWH model then detects the resulting native
weak equivalence. No condition on the source object is imposed.

The named properness proof and its clients retain the existing model,
original degree labels, cardinal, generator families and factor choices.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativePresentation

open CategoryTheory.Spectra

private theorem nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

private theorem coefficientLeftProper : IsLeftProper PointedCGWH.{u, v} := by
  change IsLeftProper (Under CGWH.point.{u, v})
  infer_instance

attribute [local instance] nativeColimits coefficientLeftProper

/-- A genuine native pushout retains all four original legs at every degree. -/
theorem isPushout_levelMap
    {A B X Y : Carrier.{u, v}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    ∀ k : OrthogonalIndex,
      IsPushout (levelMap i k) (levelMap f k) (levelMap f' k) (levelMap j k) := by
  intro k
  exact sq.map (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
    (OrthogonalOperatorIndex.ofIndex k))

/-- The same native cofibration class lies in the actual all-index coefficient class. -/
theorem cofibrations_evaluations_le :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    cofibrations Carrier.{u, v} ≤
      EvaluationTransfer.evaluationProperty
        (fun a : OrthogonalOperatorIndex.{u, v} =>
          EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) a)
        (cofibrations PointedCGWH.{u, v}) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  intro F G f hf
  rw [EvaluationTransfer.evaluationProperty_iff]
  intro a
  obtain ⟨k, rfl⟩ := ofIndex_surjective a
  exact cofibrations_levelMap f hf k

/-- The existing native orthogonal projective model is left proper on arbitrary sources. -/
theorem nativeModel_isLeftProper :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    IsLeftProper Carrier.{u, v} := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  apply EvaluationTransfer.isLeftProper_of_evaluations
    (R := fun a : OrthogonalOperatorIndex.{u, v} =>
      EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) a)
    (Q := cofibrations PointedCGWH.{u, v})
    PointedCGWH.Spectra.Orthogonal.levelModel_weakEquivalences cofibrations_evaluations_le
    (inferInstance : (weakEquivalences PointedCGWH.{u, v}).IsStableUnderCobaseChangeAgainst
      (cofibrations PointedCGWH.{u, v}))
  intro a A B X i f _ _
  infer_instance

/-- Cobase change in the original native square preserves its weak-equivalence leg. -/
theorem weakEquivalences_of_isPushout
    {A B X Y : Carrier.{u, v}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    cofibrations Carrier.{u, v} i → weakEquivalences Carrier.{u, v} f →
      weakEquivalences Carrier.{u, v} f' := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  let _ : IsLeftProper Carrier.{u, v} := nativeModel_isLeftProper
  intro hi hf
  exact IsStableUnderCobaseChangeAgainst.of_isPushout
    (inferInstance : (weakEquivalences Carrier.{u, v}).IsStableUnderCobaseChangeAgainst
      (cofibrations Carrier.{u, v})) sq hi hf

/-- The resulting weak leg and cofibration leg are detected on the same degree square. -/
theorem weakEquivalences_of_isPushout_levels
    {A B X Y : Carrier.{u, v}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    cofibrations Carrier.{u, v} i → weakEquivalences Carrier.{u, v} f →
      ∀ k : OrthogonalIndex,
        IsPushout (levelMap i k) (levelMap f k) (levelMap f' k) (levelMap j k) ∧
          weakEquivalences PointedCGWH.{u, v} (levelMap f' k) ∧
          cofibrations PointedCGWH.{u, v} (levelMap j k) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  intro hi hf k
  have hf' := weakEquivalences_of_isPushout sq hi hf
  have hj := (cofibrations Carrier.{u, v}).of_isPushout sq.flip hi
  exact ⟨isPushout_levelMap sq k, (weakEquivalences_iff f').mp hf' k,
    cofibrations_levelMap j hj k⟩

/-- The caller's chosen native pushout has the same weak-equivalence left inclusion. -/
theorem pushoutInl_weakEquivalences
    {A B X : Carrier.{u, v}} (i : A ⟶ B) (f : A ⟶ X) [HasPushout i f] :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    cofibrations Carrier.{u, v} i → weakEquivalences Carrier.{u, v} f →
      weakEquivalences Carrier.{u, v} (pushout.inl i f) :=
  weakEquivalences_of_isPushout (IsPushout.of_hasPushout i f)

end PointedCGWH.Spectra.Orthogonal.NativePresentation
