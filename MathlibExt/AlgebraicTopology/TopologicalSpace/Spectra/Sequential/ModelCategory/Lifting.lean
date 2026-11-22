/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.Generators
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

/-!
# Literal native sequential right lifting

Right lifting against the actual free images of a base family is detected
by literal level maps. The coordinate is arbitrary; native boundary and horn
specializations use the selected pointed CGWH generation data.
-/

set_option autoImplicit false

noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

namespace PointedCGWH.SequentialSpectrum

/-- Right lifting against all literal free images is exactly levelwise right
lifting against the actual base morphism family. -/
theorem liftedGenerators_rlp_iff (K : PointedCGWH.{u, v})
    (P : MorphismProperty PointedCGWH.{u, v})
    {X Y : CategoryTheory.Spectra.Sequential.Spectrum (C := PointedCGWH.{u, v}) K} (p : X ⟶ Y) :
    (liftedGenerators K P).rlp p ↔ ∀ n : ℕ,
        P.rlp (CategoryTheory.Spectra.Sequential.levelMap p n) := by
  let L : ℕ → PointedCGWH.{u, v} ⥤
      CategoryTheory.Spectra.Sequential.Spectrum (C := PointedCGWH.{u, v}) K :=
    fun n => freeAt K n
  let R : ℕ → CategoryTheory.Spectra.Sequential.Spectrum
      (C := PointedCGWH.{u, v}) K ⥤ PointedCGWH.{u, v} :=
    fun n => CategoryTheory.Spectra.Sequential.evaluation K n
  change (MorphismProperty.adjointFamilyGenerators L P).rlp p ↔
    ∀ n : ℕ, P.rlp ((R n).map p)
  exact MorphismProperty.adjointFamilyGenerators_rlp_iff L R
    (fun n => freeAtEvaluationAdjunction K n) P p

/-- The selected literal boundary family detects pointed trivial fibrations
on every actual level map. -/
theorem boundaryGenerators_rlp_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y) :
    boundaryGenerators.rlp p ↔
      ∀ n : ℕ, trivialFibrations PointedCGWH.{u, v} (levelMap p n) := by
  let G := PointedCGWH.cofibrantGenerationData.{u, v}
  change (liftedGenerators PointedCGWH.sphereOne G.I).rlp p ↔ _
  rw [liftedGenerators_rlp_iff, G.I_rlp]

/-- The selected literal horn family detects pointed fibrations on every
actual level map. -/
theorem hornGenerators_rlp_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y) :
    hornGenerators.rlp p ↔
      ∀ n : ℕ, fibrations PointedCGWH.{u, v} (levelMap p n) := by
  let G := PointedCGWH.cofibrantGenerationData.{u, v}
  change (liftedGenerators PointedCGWH.sphereOne G.J).rlp p ↔ _
  rw [liftedGenerators_rlp_iff, G.J_rlp]

end PointedCGWH.SequentialSpectrum
