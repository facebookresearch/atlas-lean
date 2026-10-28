/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightMatrixCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingPairNumerator

/-! Every entry of the complete actual matrix follows from original frame and pair coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Exact integer numerators of the complete actual post-triality matrix. -/
def generatedFifthRootEightMatrixNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 1, 0, 0,
  0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0], ![0, 1, 6, 0, 0, 0, 0, 0, -1, 0,
  0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0], ![0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0,
  0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 5,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, -1, -1, 0, 0, 0, 0, 0, 6, 0, 0, -1, 0,
  0, 0, 0, 1, -1, 1, 1, -1, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 6, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0], ![0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0,
  0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0,
  0, 0], ![0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 5, -2, 1, 1, -1, 0, -1, 0], ![0,
  1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -2, 5, -1, -1, 1, 0, 1, 0], ![0, -1, -1, 0, 0,
  0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 1, -1, 6, 1, -1, 0, -1, 0], ![0, -1, -1, 0, 0, 0, 0, 0, 1,
  0, 0, -1, 0, 0, 0, 0, 1, -1, 1, 6, -1, 0, -1, 0], ![0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0,
  0, 0, -1, 1, -1, -1, 6, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 5, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 6, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5]]

/-- The original candidate matrix is symmetric in its actual physical coordinates. -/
theorem generatedFifthRootEight_matrix_numerator_symmetric (i j : Fin 24) :
    generatedFifthRootEightMatrixNumerator i j = generatedFifthRootEightMatrixNumerator j i := by
  revert i j
  decide +kernel

/-- Every candidate diagonal is the previously certified actual original diagonal. -/
theorem generatedFifthRootEight_matrix_numerator_diagonal (i : Fin 24) :
    generatedFifthRootEightMatrixNumerator i i = generatedFifthRootEightDiagonalNumerator i := by
  revert i
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check all 276 original pair sums against the complete integer source-coefficient formula.
/-- Every candidate off-diagonal is the exact sum of the two genuine incoming signed pair rows. -/
theorem generatedFifthRootEight_matrix_numerator_pair (p : Fin 276) :
    generatedFifthRootEightIncomingPairNumerator 0 p +
      generatedFifthRootEightIncomingPairNumerator 1 p =
      2 * generatedFifthRootEightMatrixNumerator
        (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 := by
  revert p
  decide +kernel

/-- The entire actual matrix, including every zero and central sign, has the certified entries. -/
theorem generatedFifthRootEight_matrix_actual :
    (griessConwayEncode generatedFifthRootEightAxis).1 =
      fun i j => (generatedFifthRootEightMatrixNumerator i j : ℝ) / 16 := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [generatedFifthRootEight_matrix_diagonal, generatedFifthRootEight_matrix_numerator_diagonal]
  · rw [generatedFifthRootEightAxis_local_expression,
      generatedFourth_triality_matrix_off_diagonal _ i j hij,
      generatedFifthRootEight_incoming_pair_numerator,
        generatedFifthRootEight_incoming_pair_numerator]
    let p := griessPairIndex i j hij
    have hp : generatedFifthRootEightIncomingPairNumerator 0 p +
        generatedFifthRootEightIncomingPairNumerator 1 p =
        2 * generatedFifthRootEightMatrixNumerator i j := by
      have h := generatedFifthRootEight_matrix_numerator_pair p
      dsimp only [p] at h
      rw [generatedAxisGlobalPairCoordinates_actual, griessPairIndex_coordinates] at h
      by_cases hl : i < j
      · simpa only [hl, ite_true] using h
      · simpa only [hl, ite_false, generatedFifthRootEight_matrix_numerator_symmetric j i] using h
    calc
      _ = ((generatedFifthRootEightIncomingPairNumerator 0 p +
          generatedFifthRootEightIncomingPairNumerator 1 p : ℤ) : ℝ) / 32 := by push_cast; ring
      _ = (generatedFifthRootEightMatrixNumerator i j : ℝ) / 16 := by
        rw [hp]
        push_cast
        ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
