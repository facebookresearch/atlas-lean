/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFrameAction

/-! Exact rational entries of the complete original incoming matrix constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The rational diagonal weights of the genuine fifth starting matrix. -/
def generatedFifthRootEightStartingDiagonalQ (t : Fin 24) : ℚ :=
  if Nat.testBit 0x0f000f t.val then 1 / 2 else 1 / 4

/-- The complete original matrix after the actual root-8 local word, in rational coordinates. -/
def generatedFifthRootEightIncomingMatrixQ (i j : Fin 24) : ℚ :=
  ∑ t : Fin 24, generatedFifthRootEightStartingDiagonalQ t *
    ((generatedFifthRootEightFrameData 7 t i : ℚ) / 8) *
    ((generatedFifthRootEightFrameData 7 t j : ℚ) / 8)

/-- Every incoming real matrix coordinate equals its exact rational original-word formula. -/
theorem generatedFifthRootEight_incoming_matrix_coordinate (i j : Fin 24) :
    (griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)).1 i j =
      (generatedFifthRootEightIncomingMatrixQ i j : ℝ) := by
  rw [generatedFifthRootEightLocal, generatedAxisGlobalFifthShortWord_matrix_entry]
  have hi (t : Fin 24) :
      (generatedAxisGlobalFifthShortSpatialWord 8).val.symm (Pi.single i 1) t =
        (generatedFifthRootEightFrameData 7 t i : ℝ) / 8 :=
    generatedFifthRootEight_inverse_matrix_coordinate t i
  have hj (t : Fin 24) :
      (generatedAxisGlobalFifthShortSpatialWord 8).val.symm (Pi.single j 1) t =
        (generatedFifthRootEightFrameData 7 t j : ℝ) / 8 :=
    generatedFifthRootEight_inverse_matrix_coordinate t j
  simp_rw [hi, hj]
  rw [generatedFifthRootEightIncomingMatrixQ]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  cases hb : Nat.testBit 0x0f000f t.val <;>
    simp [generatedFifthRootEightStartingDiagonalQ, generatedAxisGlobalFifthMatrixDiagonal, hb]

/-- Triality preserves every actual diagonal entry of this complete packet. -/
theorem generatedFifthRootEight_matrix_diagonal_coordinate (i : Fin 24) :
    (griessConwayEncode generatedFifthRootEightAxis).1 i i =
      (generatedFifthRootEightIncomingMatrixQ i i : ℝ) := by
  rw [generatedFifthRootEightAxis_local_expression, generatedAxisGlobalRawTrialityFormula_actual]
  change generatedAxisGlobalRawTrialityMatrix
    (griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)) i i = _
  rw [generatedAxisGlobalRawTrialityMatrix, dite_eq_left rfl]
  exact generatedFifthRootEight_incoming_matrix_coordinate i i


/-- The actual physical diagonal numerators, retaining the distinguished coordinate positions. -/
def generatedFifthRootEightDiagonalNumerator : Fin 24 → ℤ :=
  ![5, 6, 6, 5, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 5, 5, 5, 5, 6, 6, 6, 5, 6, 5]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all twenty-four rational entries against the complete original frame formula.
/-- The finite diagonal table equals every original rational frame pairing. -/
theorem generatedFifthRootEight_incoming_diagonal_checked (i : Fin 24) :
    generatedFifthRootEightIncomingMatrixQ i i =
      (generatedFifthRootEightDiagonalNumerator i : ℚ) / 16 := by
  revert i
  decide +kernel

/-- Every actual final diagonal coordinate has its certified original integer numerator. -/
theorem generatedFifthRootEight_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedFifthRootEightAxis).1 i i =
      (generatedFifthRootEightDiagonalNumerator i : ℝ) / 16 := by
  rw [generatedFifthRootEight_matrix_diagonal_coordinate,
    generatedFifthRootEight_incoming_diagonal_checked]
  push_cast
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
