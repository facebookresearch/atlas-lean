/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhFrameAction

/-! Exact rational entries of the complete original incoming matrix constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The rational diagonal weights of the genuine fifth starting matrix. -/
def generatedEleventhStartingDiagonalQ (t : Fin 24) : ℚ :=
  if Nat.testBit 0x0f000f t.val then 1 / 2 else 1 / 4

/-- The complete original matrix after the actual root-3 local word, in rational coordinates. -/
def generatedEleventhIncomingMatrixQ (i j : Fin 24) : ℚ :=
  ∑ t : Fin 24, generatedEleventhStartingDiagonalQ t *
    ((generatedEleventhFrameData 7 t i : ℚ) / 8) *
    ((generatedEleventhFrameData 7 t j : ℚ) / 8)

/-- Every incoming real matrix coordinate equals its exact rational original-word formula. -/
theorem generatedEleventh_incoming_matrix_coordinate (i j : Fin 24) :
    (griessConwayEncode (rhoLocal generatedEleventhLocal generatedFifthAxis)).1 i j =
      (generatedEleventhIncomingMatrixQ i j : ℝ) := by
  rw [generatedEleventhLocal, generatedAxisGlobalFifthShortWord_matrix_entry]
  have hi (t : Fin 24) :
      (generatedAxisGlobalFifthShortSpatialWord 3).val.symm (Pi.single i 1) t =
        (generatedEleventhFrameData 7 t i : ℝ) / 8 :=
    generatedEleventh_inverse_matrix_coordinate t i
  have hj (t : Fin 24) :
      (generatedAxisGlobalFifthShortSpatialWord 3).val.symm (Pi.single j 1) t =
        (generatedEleventhFrameData 7 t j : ℝ) / 8 :=
    generatedEleventh_inverse_matrix_coordinate t j
  simp_rw [hi, hj]
  rw [generatedEleventhIncomingMatrixQ]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  cases hb : Nat.testBit 0x0f000f t.val <;>
    simp [generatedEleventhStartingDiagonalQ, generatedAxisGlobalFifthMatrixDiagonal, hb]

/-- Triality preserves every actual diagonal entry of this complete packet. -/
theorem generatedEleventh_matrix_diagonal_coordinate (i : Fin 24) :
    (griessConwayEncode generatedEleventhAxis).1 i i =
      (generatedEleventhIncomingMatrixQ i i : ℝ) := by
  rw [generatedEleventhAxis_local_expression, generatedAxisGlobalRawTrialityFormula_actual]
  change generatedAxisGlobalRawTrialityMatrix
    (griessConwayEncode (rhoLocal generatedEleventhLocal generatedFifthAxis)) i i = _
  rw [generatedAxisGlobalRawTrialityMatrix, dite_eq_left rfl]
  exact generatedEleventh_incoming_matrix_coordinate i i


/-- The actual physical diagonal numerators, retaining the distinguished coordinate positions. -/
def generatedEleventhDiagonalNumerator : Fin 24 → ℤ :=
  ![11, 11, 11, 11, 11, 11, 11, 11, 9, 9, 9, 9, 9, 9, 13, 13, 11, 11, 11, 11, 11, 11, 11, 11]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all twenty-four rational entries against the complete original frame formula.
/-- The finite diagonal table equals every original rational frame pairing. -/
theorem generatedEleventh_incoming_diagonal_checked (i : Fin 24) :
    generatedEleventhIncomingMatrixQ i i =
      (generatedEleventhDiagonalNumerator i : ℚ) / 32 := by
  revert i
  decide +kernel

/-- Every actual final diagonal coordinate has its certified original integer numerator. -/
theorem generatedEleventh_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedEleventhAxis).1 i i =
      (generatedEleventhDiagonalNumerator i : ℝ) / 32 := by
  rw [generatedEleventh_matrix_diagonal_coordinate, generatedEleventh_incoming_diagonal_checked]
  push_cast
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
