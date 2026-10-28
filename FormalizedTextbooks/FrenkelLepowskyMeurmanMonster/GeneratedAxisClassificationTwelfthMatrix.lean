/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingPairNumerator

/-! Every entry of the complete actual matrix follows from original frame and pair coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Exact integer numerators of the complete actual post-triality matrix. -/
def generatedTwelfthMatrixNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![5, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
    ![0, 5, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![1, 1, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 1, -1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, -1, -1, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 7, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 7, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5]
  ]

/-- The original candidate matrix is symmetric in its actual physical coordinates. -/
theorem generatedTwelfth_matrix_numerator_symmetric (i j : Fin 24) :
    generatedTwelfthMatrixNumerator i j = generatedTwelfthMatrixNumerator j i := by
  revert i j
  decide +kernel

/-- Every candidate diagonal is the previously certified actual original diagonal. -/
theorem generatedTwelfth_matrix_numerator_diagonal (i : Fin 24) :
    generatedTwelfthMatrixNumerator i i = generatedTwelfthDiagonalNumerator i := by
  revert i
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check all 276 original pair sums against the complete integer source-coefficient formula.
/-- Every candidate off-diagonal is the exact sum of the two genuine incoming signed pair rows. -/
theorem generatedTwelfth_matrix_numerator_pair (p : Fin 276) :
    generatedTwelfthIncomingPairNumerator 0 p + generatedTwelfthIncomingPairNumerator 1 p =
      2 * generatedTwelfthMatrixNumerator
        (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 := by
  revert p
  decide +kernel

/-- The entire actual matrix, including every zero and central sign, has the certified entries. -/
theorem generatedTwelfth_matrix_actual :
    (griessConwayEncode generatedTwelfthAxis).1 =
      fun i j => (generatedTwelfthMatrixNumerator i j : ℝ) / 16 := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [generatedTwelfth_matrix_diagonal, generatedTwelfth_matrix_numerator_diagonal]
  · rw [generatedTwelfthAxis_local_expression,
      generatedFourth_triality_matrix_off_diagonal _ i j hij,
      generatedTwelfth_incoming_pair_numerator, generatedTwelfth_incoming_pair_numerator]
    let p := griessPairIndex i j hij
    have hp : generatedTwelfthIncomingPairNumerator 0 p +
        generatedTwelfthIncomingPairNumerator 1 p =
        2 * generatedTwelfthMatrixNumerator i j := by
      have h := generatedTwelfth_matrix_numerator_pair p
      dsimp only [p] at h
      rw [generatedAxisGlobalPairCoordinates_actual, griessPairIndex_coordinates] at h
      by_cases hl : i < j
      · simpa only [hl, ite_true] using h
      · simpa only [hl, ite_false, generatedTwelfth_matrix_numerator_symmetric j i] using h
    calc
      _ = ((generatedTwelfthIncomingPairNumerator 0 p +
          generatedTwelfthIncomingPairNumerator 1 p : ℤ) : ℝ) / 32 := by push_cast; ring
      _ = (generatedTwelfthMatrixNumerator i j : ℝ) / 16 := by
        rw [hp]
        push_cast
        ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
