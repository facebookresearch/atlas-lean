/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor

/-! Actual spatial fixation joins full short and tensor certificates for the original sixth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Each of the five corrected actual fibers fixes the entire original matrix constituent. -/
theorem generatedSixth_corrected_generator_matrix_fixed (k : Fin 5) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedSixthCorrectedGenerator k)) generatedSixthAxis)).1 =
        (griessConwayEncode generatedSixthAxis).1 := by
  have he : sixthFrameOrbitOriginalIsometry (Fin.natAdd 10 k) =
      (generatedSixthRawGenerator k).val.2 := by
    fin_cases k <;> rfl
  have hg := sixthFrameOrbit_original_spatial_mem (Fin.natAdd 10 k)
  change conwayMatrixAction (sixthFrameOrbitOriginalIsometry (Fin.natAdd 10 k))
    (griessConwayEncode generatedSixthAxis).1 = (griessConwayEncode generatedSixthAxis).1 at hg
  rw [he] at hg
  rw [generatedFourth_local_matrix, generatedSixth_corrected_generator_spatial]
  exact hg

/-- Full original short and tensor fixation suffice for actual entire-axis fixation. -/
theorem generatedSixth_corrected_generator_full_fixed_of_blocks (k : Fin 5)
    (hs : localShortOperator (generatedSixthCorrectedGenerator k)
      (griessConwayEncode generatedSixthAxis).2.1 = (griessConwayEncode generatedSixthAxis).2.1)
    (ht : localTensorRepresentation (generatedSixthCorrectedGenerator k)
      (griessConwayEncode generatedSixthAxis).2.2 = (griessConwayEncode generatedSixthAxis).2.2) :
    rhoLocal (localFiberIntoH (generatedSixthCorrectedGenerator k)) generatedSixthAxis =
      generatedSixthAxis := by
  apply Function.LeftInverse.injective griessConwayDecode_encode
  apply Prod.ext
  · exact generatedSixth_corrected_generator_matrix_fixed k
  · apply Prod.ext
    · rw [generatedFourth_local_short]
      exact hs
    · rw [generatedFourth_local_tensor]
      exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
