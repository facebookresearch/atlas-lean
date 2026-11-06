/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthPairZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthDiagonal

/-! The entire actual eighth matrix is diagonal, with its exact entries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full original matrix, without a classification or spectral assumption. -/
def generatedEighthAxisMatrix (i j : Fin 24) : ℝ :=
  if i ≠ j then 0 else
    if i = 20 then 3 / 4 else
      if i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨
          i = 9 ∨ i = 10 ∨ i = 16 ∨ i = 18 ∨ i = 22 ∨ i = 23 then 3 / 8 else 1 / 4

/-- Every off-diagonal original matrix coordinate is zero. -/
theorem generatedEighth_matrix_off_diagonal (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode generatedEighthAxis).1 i j = 0 := by
  rw [generatedEighthAxis_local_expression,
    generatedFourth_triality_matrix_off_diagonal _ i j hij,
    generatedEighth_middle_pair_zero, generatedEighth_middle_pair_zero]
  norm_num

/-- Every entry of the actual eighth prototype matrix is certified. -/
theorem generatedEighth_axis_matrix :
    (griessConwayEncode generatedEighthAxis).1 = generatedEighthAxisMatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [generatedEighth_matrix_diagonal]
    simp only [generatedEighthAxisMatrix, ne_eq, not_true_eq_false, ite_false]
  · rw [generatedEighth_matrix_off_diagonal i j hij]
    simp only [generatedEighthAxisMatrix, hij, ne_eq, not_false_eq_true, ite_true]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
