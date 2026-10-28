/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowIntegral

/-! Six finite original arithmetic equalities bind an actual preferred target and its complete
signed coefficient. No binary equality supplies a central phase: the sixth equality is separate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original integer, intrinsic binary, actual image and full central phase obligations
for a row. -/
structure GeneratedNinthShortRowCertificate (k : Fin 4136) : Prop where
  /-- The displayed source coordinates multiply by the genuine integer Leech basis to its vector. -/
  sourceInteger : generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
    leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k
  /-- The displayed target coordinates multiply by the genuine integer Leech basis to its vector. -/
  targetInteger : generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
    leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k
  /-- The source intrinsic mask is its actual hyperbolic binary coordinate vector. -/
  sourceBinary : leechHyperbolicInverse *ᵥ integerParity
      (generatedNinthShortRowSourceCoordinates k) =
    monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k)
  /-- The target intrinsic mask is its actual hyperbolic binary coordinate vector. -/
  targetBinary : leechHyperbolicInverse *ᵥ integerParity
      (generatedNinthShortRowTargetCoordinates k) =
    monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k)
  /-- The original word’s checked binary action carries the source mask to the target mask. -/
  image : sixthFrameOrbitMaskApply generatedNinthQBinaryColumns
      (generatedNinthShortRowSourceMask k) = generatedNinthShortRowTargetMask k
  /-- The complete original central phase agrees with the displayed scalar bit. -/
  phase : generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
    generatedNinthShortRowPhase k

/-- The row's integer and binary certificates identify its genuine full source preferred lift. -/
theorem generatedNinth_short_row_source_mask (k : Fin 4136)
    (h : GeneratedNinthShortRowCertificate k) :
    toAdd (generatedNinthOriginalShortQ (generatedNinthShortRowSource k)).base =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  apply generatedNinth_original_short_mask_of_coordinates
    (generatedNinthShortRowSource k) (generatedNinthShortRowSourceCoordinates k)
  · rw [← generatedNinth_short_row_source_integral_actual]
    exact h.sourceInteger
  · exact h.sourceBinary

/-- The row's integer and binary certificates identify its actual target preferred lift. -/
theorem generatedNinth_short_row_target_mask (k : Fin 4136)
    (h : GeneratedNinthShortRowCertificate k) :
    toAdd (monsterNortonShortQ (generatedNinthShortRowTarget k)).base =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  apply generatedNinth_preferred_short_mask_of_coordinates
    (generatedNinthShortRowTarget k) (generatedNinthShortRowTargetCoordinates k)
  · rw [← generatedNinth_short_row_target_integral_actual]
    exact h.targetInteger
  · exact h.targetBinary

/-- A complete row certificate binds the target to the original nine-factor spatial word. -/
theorem generatedNinth_short_row_target_actual (k : Fin 4136)
    (h : GeneratedNinthShortRowCertificate k) :
    generatedNinthMiddleShortSourceIndex (generatedNinthShortRowSource k) =
      generatedNinthShortRowTarget k :=
  generatedNinth_original_short_image_of_masks _ _ _ _
    (generatedNinth_short_row_source_mask k h) (generatedNinth_short_row_target_mask k h) h.image

/-- A complete row certificate gives the actual coefficient with its original central phase. -/
theorem generatedNinth_short_row_coefficient_actual (k : Fin 4136)
    (h : GeneratedNinthShortRowCertificate k) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (generatedNinthShortRowTarget k) =
        qSign (generatedNinthShortRowPhase k) *
          ((generatedNinthOriginalShortNumerator (generatedNinthShortRowSource k) : ℝ) / 16) := by
  rw [generatedNinth_original_short_coefficient_of_mask_phase _ _ _ _
    (generatedNinth_short_row_source_mask k h) (generatedNinth_short_row_target_mask k h) h.image,
    h.phase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
