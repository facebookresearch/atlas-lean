/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQBinaryCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortImageRecognition

/-! Three checked packed equations identify a genuine preferred short target. The source and
 target masks denote intrinsic lifts, and the phase remains the original source cochain. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Source and target intrinsic masks together with an actual column equation recognize the row. -/
theorem generatedNinth_original_short_image_of_masks
    (a : generatedNinthOriginalShortLabel) (s : GriessShortIndex) (n m : ℕ)
    (hsource : toAdd (generatedNinthOriginalShortQ a).base =
      monsterCo1GeometryBinaryMaskDecode n)
    (htarget : toAdd (monsterNortonShortQ s).base =
      monsterCo1GeometryBinaryMaskDecode m)
    (himage : sixthFrameOrbitMaskApply generatedNinthQBinaryColumns n = m) :
    generatedNinthMiddleShortSourceIndex a = s := by
  apply generatedNinth_original_short_image_of_base
  apply toAdd.injective
  rw [generatedNinth_Q_binary_mask_evaluation n _ hsource, himage, htarget]

/-- A recognized packed target has its complete actual signed coefficient, with no phase omitted. -/
theorem generatedNinth_original_short_coefficient_of_masks
    (a : generatedNinthOriginalShortLabel) (s : GriessShortIndex) (n m : ℕ)
    (hsource : toAdd (generatedNinthOriginalShortQ a).base =
      monsterCo1GeometryBinaryMaskDecode n)
    (htarget : toAdd (monsterNortonShortQ s).base =
      monsterCo1GeometryBinaryMaskDecode m)
    (himage : sixthFrameOrbitMaskApply generatedNinthQBinaryColumns n = m) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 s =
        qSign (generatedNinthSelectedPhase (generatedNinthOriginalShortQ a)) *
          ((generatedNinthOriginalShortNumerator a : ℝ) / 16) := by
  rw [← generatedNinth_original_short_image_of_masks a s n m hsource htarget himage,
    generatedNinth_middle_short_source_coefficient, ← generatedNinth_original_short_Q_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
