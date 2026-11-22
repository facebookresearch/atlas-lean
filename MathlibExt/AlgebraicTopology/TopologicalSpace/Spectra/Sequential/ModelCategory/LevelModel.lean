/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.Lifting
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelModel

/-!
# The native sequential projective level model

The sole model value is `PointedCGWH.Spectra.Sequential.levelModel`, constructed
by the native generator-cardinal enriched projective factory. This module
retains the original boundary and horn class readbacks for that value.
The canonical factory supplies the original ordinal choice internally.
-/

set_option autoImplicit false

noncomputable section
universe u v

open CategoryTheory Limits HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

namespace PointedCGWH.SequentialSpectrum

/-- Weak equivalences detected by every actual native level map. -/
def levelWeakEquivalences : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  fun _ _ f => ∀ n : ℕ, weakEquivalences PointedCGWH.{u, v} (levelMap f n)

private theorem nativeEvaluationProperty_iff
    (P : MorphismProperty PointedCGWH.{u, v})
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    EvaluationTransfer.evaluationProperty
        (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} =>
          EnrichedFunctorCat.evaluation a) P f ↔
      ∀ n : ℕ, P (levelMap f n) := by
  rw [EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
  · intro h a
    exact h a.degree

/-- Cofibrations in the actual returned level model are the boundary-generated
left class. -/
theorem levelModelCategory_cofibrations :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithCofibrations.cofibrations =
      boundaryGenerators.{u, v}.rlp.llp := by
  rw [PointedCGWH.Spectra.Sequential.levelModel_cofibrations]
  rw [show boundaryGenerators.{u, v} =
    EnrichedProjective.generators (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
      PointedCGWH.cofibrantGenerationData.{u, v}.I from
    liftedGenerators_eq_enrichedGenerators PointedCGWH.sphereOne
      PointedCGWH.cofibrantGenerationData.{u, v}.I]

/-- Fibrations in the actual returned level model are exactly level fibrations. -/
theorem levelModelCategory_fibrations_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithFibrations.fibrations f ↔
      ∀ n : ℕ, fibrations PointedCGWH.{u, v} (levelMap f n) := by
  rw [PointedCGWH.Spectra.Sequential.levelModel_fibrations]
  exact nativeEvaluationProperty_iff (fibrations PointedCGWH.{u, v}) f

/-- Weak equivalences in the actual returned model are exactly level weak
equivalences. -/
theorem levelModelCategory_weakEquivalences_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences f ↔
      ∀ n : ℕ, weakEquivalences PointedCGWH.{u, v} (levelMap f n) := by
  let d := PointedCGWH.Spectra.Sequential.levelModel.{u, v}
  change d.categoryWithWeakEquivalences.weakEquivalences f ↔ _
  rw [PointedCGWH.Spectra.Sequential.levelModel_weakEquivalences]
  exact nativeEvaluationProperty_iff (weakEquivalences PointedCGWH.{u, v}) f

/-- Trivial fibrations in the actual returned level model are detected by the
literal boundary family. -/
theorem levelModelCategory_trivialFibrations :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithFibrations.fibrations ⊓
      (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences =
        boundaryGenerators.{u, v}.rlp := by
  ext X Y f
  change ((PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithFibrations.fibrations f ∧
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences f) ↔ _
  rw [levelModelCategory_fibrations_iff, levelModelCategory_weakEquivalences_iff,
    boundaryGenerators_rlp_iff]
  constructor
  · rintro ⟨hf, hw⟩ n
    exact ⟨hf n, hw n⟩
  · intro h
    exact ⟨fun n => (h n).1, fun n => (h n).2⟩

end PointedCGWH.SequentialSpectrum
