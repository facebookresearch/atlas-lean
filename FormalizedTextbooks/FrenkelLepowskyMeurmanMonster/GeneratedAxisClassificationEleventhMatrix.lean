/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhIncomingPairNumerator

/-! Every entry of the complete actual matrix follows from original frame and pair coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Exact integer numerators of the complete actual post-triality matrix. -/
def generatedEleventhMatrixNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![11, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 11, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -2, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -2, 2, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 11, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 11, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, 2, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, -4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 9, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2, 2, -2, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, 2, -2, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, -2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 11, -2, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 11, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 2, 11, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, -2, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 11, -2, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 11, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 2, 11]
  ]

/-- The original candidate matrix is symmetric in its actual physical coordinates. -/
theorem generatedEleventh_matrix_numerator_symmetric (i j : Fin 24) :
    generatedEleventhMatrixNumerator i j = generatedEleventhMatrixNumerator j i := by
  revert i j
  decide +kernel

/-- Every candidate diagonal is the previously certified actual original diagonal. -/
theorem generatedEleventh_matrix_numerator_diagonal (i : Fin 24) :
    generatedEleventhMatrixNumerator i i = generatedEleventhDiagonalNumerator i := by
  revert i
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check all 276 original pair sums against the complete integer source-coefficient formula.
/-- Every candidate off-diagonal is the exact sum of the two genuine incoming signed pair rows. -/
theorem generatedEleventh_matrix_numerator_pair (p : Fin 276) :
    generatedEleventhIncomingPairNumerator 0 p + generatedEleventhIncomingPairNumerator 1 p =
      1 * generatedEleventhMatrixNumerator
        (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 := by
  revert p
  decide +kernel

/-- The entire actual matrix, including every zero and central sign, has the certified entries. -/
theorem generatedEleventh_matrix_actual :
    (griessConwayEncode generatedEleventhAxis).1 =
      fun i j => (generatedEleventhMatrixNumerator i j : ℝ) / 32 := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [generatedEleventh_matrix_diagonal, generatedEleventh_matrix_numerator_diagonal]
  · rw [generatedEleventhAxis_local_expression,
      generatedFourth_triality_matrix_off_diagonal _ i j hij,
      generatedEleventh_incoming_pair_numerator, generatedEleventh_incoming_pair_numerator]
    let p := griessPairIndex i j hij
    have hp : generatedEleventhIncomingPairNumerator 0 p +
        generatedEleventhIncomingPairNumerator 1 p =
        1 * generatedEleventhMatrixNumerator i j := by
      have h := generatedEleventh_matrix_numerator_pair p
      dsimp only [p] at h
      rw [generatedAxisGlobalPairCoordinates_actual, griessPairIndex_coordinates] at h
      by_cases hl : i < j
      · simpa only [hl, ite_true] using h
      · simpa only [hl, ite_false, generatedEleventh_matrix_numerator_symmetric j i] using h
    calc
      _ = ((generatedEleventhIncomingPairNumerator 0 p +
          generatedEleventhIncomingPairNumerator 1 p : ℤ) : ℝ) / 32 := by push_cast; ring
      _ = (generatedEleventhMatrixNumerator i j : ℝ) / 32 := by
        rw [hp]
        push_cast
        ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
