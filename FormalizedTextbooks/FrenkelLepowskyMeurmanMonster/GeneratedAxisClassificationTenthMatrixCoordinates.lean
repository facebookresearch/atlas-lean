/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFrameAction

/-! Exact rational entries of the complete original incoming matrix constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The rational diagonal weights of the genuine fifth starting matrix. -/
def generatedTenthStartingDiagonalQ (t : Fin 24) : ℚ :=
  if Nat.testBit 0x0f000f t.val then 1 / 2 else 1 / 4

/-- The complete original matrix after the actual root-2 local word, in rational coordinates. -/
def generatedTenthIncomingMatrixQ (i j : Fin 24) : ℚ :=
  ∑ t : Fin 24, generatedTenthStartingDiagonalQ t *
    ((generatedTenthFrameData 7 t i : ℚ) / 8) *
    ((generatedTenthFrameData 7 t j : ℚ) / 8)

/-- Every incoming real matrix coordinate equals its exact rational original-word formula. -/
theorem generatedTenth_incoming_matrix_coordinate (i j : Fin 24) :
    (griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis)).1 i j =
      (generatedTenthIncomingMatrixQ i j : ℝ) := by
  rw [generatedTenthLocal, generatedAxisGlobalFifthShortWord_matrix_entry]
  have hi (t : Fin 24) :
      (generatedAxisGlobalFifthShortSpatialWord 2).val.symm (Pi.single i 1) t =
        (generatedTenthFrameData 7 t i : ℝ) / 8 :=
    generatedTenth_inverse_matrix_coordinate t i
  have hj (t : Fin 24) :
      (generatedAxisGlobalFifthShortSpatialWord 2).val.symm (Pi.single j 1) t =
        (generatedTenthFrameData 7 t j : ℝ) / 8 :=
    generatedTenth_inverse_matrix_coordinate t j
  simp_rw [hi, hj]
  rw [generatedTenthIncomingMatrixQ]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  cases hb : Nat.testBit 0x0f000f t.val <;>
    simp [generatedTenthStartingDiagonalQ, generatedAxisGlobalFifthMatrixDiagonal, hb]

/-- Triality preserves every actual diagonal entry of this complete packet. -/
theorem generatedTenth_matrix_diagonal_coordinate (i : Fin 24) :
    (griessConwayEncode generatedTenthAxis).1 i i =
      (generatedTenthIncomingMatrixQ i i : ℝ) := by
  rw [generatedTenthAxis_local_expression, generatedAxisGlobalRawTrialityFormula_actual]
  change generatedAxisGlobalRawTrialityMatrix
    (griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis)) i i = _
  rw [generatedAxisGlobalRawTrialityMatrix, dite_eq_left rfl]
  exact generatedTenth_incoming_matrix_coordinate i i


/-- The actual physical diagonal numerators, retaining the distinguished coordinate positions. -/
def generatedTenthDiagonalNumerator : Fin 24 → ℤ :=
  ![11, 9, 9, 11, 11, 11, 11, 11, 9, 11, 11, 9, 11, 11, 11, 11, 9, 13, 11, 11, 11, 9, 11, 13]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all twenty-four rational entries against the complete original frame formula.
/-- The finite diagonal table equals every original rational frame pairing. -/
theorem generatedTenth_incoming_diagonal_checked (i : Fin 24) :
    generatedTenthIncomingMatrixQ i i =
      (generatedTenthDiagonalNumerator i : ℚ) / 32 := by
  revert i
  decide +kernel

/-- Every actual final diagonal coordinate has its certified original integer numerator. -/
theorem generatedTenth_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedTenthAxis).1 i i =
      (generatedTenthDiagonalNumerator i : ℝ) / 32 := by
  rw [generatedTenth_matrix_diagonal_coordinate, generatedTenth_incoming_diagonal_checked]
  push_cast
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
