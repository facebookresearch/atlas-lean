/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthIncomingPairNumerator

/-! Every entry of the complete actual matrix follows from original frame and pair coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Exact integer numerators of the complete actual post-triality matrix. -/
def generatedTenthMatrixNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![11, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 11, 0, 0, 2, 0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 11, 0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 11, -2, 0, 0, -2, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -2, 11, 0, 0, 2, 0, 0, 0, 0, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 13, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 11, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 11, 0],
    ![0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 13]
  ]

/-- The original candidate matrix is symmetric in its actual physical coordinates. -/
theorem generatedTenth_matrix_numerator_symmetric (i j : Fin 24) :
    generatedTenthMatrixNumerator i j = generatedTenthMatrixNumerator j i := by
  revert i j
  decide +kernel

/-- Every candidate diagonal is the previously certified actual original diagonal. -/
theorem generatedTenth_matrix_numerator_diagonal (i : Fin 24) :
    generatedTenthMatrixNumerator i i = generatedTenthDiagonalNumerator i := by
  revert i
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check all 276 original pair sums against the complete integer source-coefficient formula.
/-- Every candidate off-diagonal is the exact sum of the two genuine incoming signed pair rows. -/
theorem generatedTenth_matrix_numerator_pair (p : Fin 276) :
    generatedTenthIncomingPairNumerator 0 p + generatedTenthIncomingPairNumerator 1 p =
      1 * generatedTenthMatrixNumerator
        (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 := by
  revert p
  decide +kernel

/-- The entire actual matrix, including every zero and central sign, has the certified entries. -/
theorem generatedTenth_matrix_actual :
    (griessConwayEncode generatedTenthAxis).1 =
      fun i j => (generatedTenthMatrixNumerator i j : ℝ) / 32 := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [generatedTenth_matrix_diagonal, generatedTenth_matrix_numerator_diagonal]
  · rw [generatedTenthAxis_local_expression,
      generatedFourth_triality_matrix_off_diagonal _ i j hij,
      generatedTenth_incoming_pair_numerator, generatedTenth_incoming_pair_numerator]
    let p := griessPairIndex i j hij
    have hp : generatedTenthIncomingPairNumerator 0 p +
        generatedTenthIncomingPairNumerator 1 p =
        1 * generatedTenthMatrixNumerator i j := by
      have h := generatedTenth_matrix_numerator_pair p
      dsimp only [p] at h
      rw [generatedAxisGlobalPairCoordinates_actual, griessPairIndex_coordinates] at h
      by_cases hl : i < j
      · simpa only [hl, ite_true] using h
      · simpa only [hl, ite_false, generatedTenth_matrix_numerator_symmetric j i] using h
    calc
      _ = ((generatedTenthIncomingPairNumerator 0 p +
          generatedTenthIncomingPairNumerator 1 p : ℤ) : ℝ) / 32 := by push_cast; ring
      _ = (generatedTenthMatrixNumerator i j : ℝ) / 32 := by
        rw [hp]
        push_cast
        ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
