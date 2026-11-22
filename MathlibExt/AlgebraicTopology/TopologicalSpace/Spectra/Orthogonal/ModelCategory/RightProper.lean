/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.ModelCategory.NativePresentation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Right properness of the actual orthogonal native level model

The existing native all-object fibrancy theorem uses the original evaluated
Serre-fibration class and actual terminal object. The general all-fibrant
criterion proves right properness for that same model. The resulting
base-change maps are the caller's original pullback projections, and their
degree squares are preserved by genuine enriched evaluation.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativePresentation

open CategoryTheory.Spectra

/-- The actual native orthogonal level model is right proper. -/
theorem nativeModel_isRightProper :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    IsRightProper Carrier.{u, v} := by
  let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
    EnrichedProjective.Native.Construction.generatorOrderBot
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  exact isRightProper_of_all_objects_fibrant EnrichedProjective.Native.allObjectsFibrant

/-- All four original native pullback legs retain their degree square. -/
theorem isPullback_levelMap
    {A B X Y : Carrier.{u, v}} {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    ∀ k : OrthogonalIndex,
      IsPullback (levelMap p' k) (levelMap f' k) (levelMap f k) (levelMap p k) := by
  intro k
  exact sq.map (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
    (OrthogonalOperatorIndex.ofIndex k))

/-- Base change of the caller's weak equivalence along the original fibration is weak. -/
theorem weakEquivalences_of_isPullback
    {A B X Y : Carrier.{u, v}} {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    fibrations Carrier.{u, v} p → weakEquivalences Carrier.{u, v} f →
      weakEquivalences Carrier.{u, v} f' := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  let _ : IsRightProper Carrier.{u, v} := nativeModel_isRightProper
  intro hp hf
  let h : (weakEquivalences Carrier.{u, v}).IsStableUnderBaseChangeAgainst
      (fibrations Carrier.{u, v}) := inferInstance
  exact (h.isStableUnderBaseChangeAlong p hp).of_isPullback sq hf

/-- Both resulting classes use the same original degree pullback. -/
theorem weakEquivalences_of_isPullback_levels
    {A B X Y : Carrier.{u, v}} {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    fibrations Carrier.{u, v} p → weakEquivalences Carrier.{u, v} f →
      ∀ k : OrthogonalIndex,
        IsPullback (levelMap p' k) (levelMap f' k) (levelMap f k) (levelMap p k) ∧
          weakEquivalences PointedCGWH.{u, v} (levelMap f' k) ∧
          fibrations PointedCGWH.{u, v} (levelMap p' k) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  intro hp hf k
  have hf' := weakEquivalences_of_isPullback sq hp hf
  have hp' := (fibrations Carrier.{u, v}).of_isPullback sq.flip hp
  exact ⟨isPullback_levelMap sq k, (weakEquivalences_iff f').mp hf' k,
    (fibrations_iff p').mp hp' k⟩

/-- The caller's chosen pullback retains its actual weak second projection. -/
theorem pullbackSnd_weakEquivalences
    {B X Y : Carrier.{u, v}} (f : B ⟶ Y) (p : X ⟶ Y) [HasPullback f p] :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    fibrations Carrier.{u, v} p → weakEquivalences Carrier.{u, v} f →
      weakEquivalences Carrier.{u, v} (pullback.snd f p) :=
  weakEquivalences_of_isPullback (IsPullback.of_hasPullback f p)

end PointedCGWH.Spectra.Orthogonal.NativePresentation
