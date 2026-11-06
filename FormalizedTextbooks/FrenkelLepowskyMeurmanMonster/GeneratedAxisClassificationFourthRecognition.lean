/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthWatermark
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagRecognition

/-! The original fourth matrix fixes exactly the counted actual section-line flag. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The actual octad projection is the literal four-through-eleven coordinate projection. -/
theorem generatedFourth_flag_projection :
    generatedAxisE8ShortProjection generatedFourthFlagOctad =
      Matrix.diagonal (fun i : Fin 24 => if 4 ≤ i.val ∧ i.val < 12 then 1 else 0) := by
  have hb : ∀ i : Fin 24, Nat.testBit 0xff0 i.val = true ↔ 4 ≤ i.val ∧ i.val < 12 := by
    decide +kernel
  have hn (i : Fin 24) : golayOctadWord generatedFourthFlagOctad i ≠ 0 ↔
      4 ≤ i.val ∧ i.val < 12 := by
    have h := golayOctadWord_ne_zero_iff generatedFourthFlagOctad i
    simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, generatedFourthFlagOctad_mask, hb] using h
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : 4 ≤ i.val ∧ i.val < 12
  · simp [(hn i).mpr hi, hi]
  · have hz : golayOctadWord generatedFourthFlagOctad i = 0 := by
      by_contra h
      exact hi ((hn i).mp h)
    simp [hz, hi]

/-- The distinguished line is incident in the exact carrier used by the flag count. -/
theorem generatedFourth_flag_incident : generatedFourthFlagShort ∈ generatedAxisE8ShortLines
    (generatedAxisE8CoordinateSection (golayOctadWord generatedFourthFlagOctad)) := by
  rw [generatedAxisE8ShortLines_coordinate_mem]
  exact generatedFourthFlagShort_supported

/-- The original matrix is the counted actual flag matrix. -/
theorem generatedFourth_matrix_actual_flag :
    (griessConwayEncode generatedFourthAxis).1 = generatedAxisE8ShortFlagMatrix
      (generatedAxisE8ShortProjection generatedFourthFlagOctad)
      (generatedAxisE8ShortOuter generatedFourthFlagShort) := by
  rw [generatedFourth_matrix_watermark, generatedFourth_flag_projection]
  rfl

/-- Fixing the original matrix is membership in the full actual Co0 flag stabilizer. -/
theorem generatedFourth_matrix_stabilizer_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedFourthAxis).1 =
      (griessConwayEncode generatedFourthAxis).1 ↔
        g ∈ generatedAxisE8ShortFlagStabilizer
          generatedFourthFlagOctad generatedFourthFlagShort := by
  rw [generatedFourth_matrix_actual_flag]
  exact generatedAxisE8ShortFlagMatrix_stabilizer_iff _ _ generatedFourth_flag_incident g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
