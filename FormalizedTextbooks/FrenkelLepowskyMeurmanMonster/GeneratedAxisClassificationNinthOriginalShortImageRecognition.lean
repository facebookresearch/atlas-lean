/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortQCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortBaseRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleShortSupport

/-! Checked source-base images determine actual preferred target rows and their complete phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Finite actual coordinate-image evaluation recognizes the genuine preferred target source row. -/
theorem generatedNinth_original_short_image_of_base
    (a : generatedNinthOriginalShortLabel) (s : GriessShortIndex)
    (h : (generatedNinthQCoordinateEvaluation (generatedNinthOriginalShortQ a)).base =
      (monsterNortonShortQ s).base) :
    generatedNinthMiddleShortSourceIndex a = s := by
  rw [← generatedNinth_QCoordinateEvaluation_eq,
    generatedNinth_original_short_Q_actual, monsterNortonShortQ_eq] at h
  exact generatedNinth_short_image_of_base (generatedNinthOriginalShortIndex a) s h

/-- Every recognized finite source-base image has its actual full central-phase coefficient. -/
theorem generatedNinth_original_short_image_coefficient
    (a : generatedNinthOriginalShortLabel) (s : GriessShortIndex)
    (h : (generatedNinthQCoordinateEvaluation (generatedNinthOriginalShortQ a)).base =
      (monsterNortonShortQ s).base) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 s =
        qSign (generatedNinthSelectedPhase (generatedNinthOriginalShortQ a)) *
          ((generatedNinthOriginalShortNumerator a : ℝ) / 16) := by
  rw [← generatedNinth_original_short_image_of_base a s h,
    generatedNinth_middle_short_source_coefficient, ← generatedNinth_original_short_Q_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
