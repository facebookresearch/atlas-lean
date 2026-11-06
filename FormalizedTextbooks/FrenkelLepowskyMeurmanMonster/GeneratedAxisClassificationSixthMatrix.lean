/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddlePairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthDiagonal

/-! Every coordinate of the actual sixth-axis matrix is fixed by original triality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The sparse matrix of the genuine exterior-triality image, without a spectral hypothesis. -/
def generatedSixthAxisMatrix (i j : Fin 24) : ℝ :=
  if i = j then
    if i = 19 then 33 / 32 else if i = 16 ∨ i = 17 then 17 / 32 else 9 / 32
  else
    generatedSixthMiddlePairValue 0 (if i < j then i else j) (if i < j then j else i) / 2

/-- The actual off-diagonal matrix coordinates are the complete sparse pair table. -/
theorem generatedSixth_matrix_off_diagonal (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode generatedSixthAxis).1 i j =
      generatedSixthMiddlePairValue 0 (if i < j then i else j)
        (if i < j then j else i) / 2 := by
  rw [generatedSixthAxis_local_expression,
    generatedFourth_triality_matrix_off_diagonal _ i j hij,
    generatedSixth_middle_pair_coordinate, generatedSixth_middle_pair_coordinate,
    griessPairIndex_coordinates]
  split_ifs <;> simp [generatedSixthMiddlePairValue]

/-- The full original matrix watermark is unconditional for this literal generated word. -/
theorem generatedSixth_axis_matrix :
    (griessConwayEncode generatedSixthAxis).1 = generatedSixthAxisMatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [generatedSixth_matrix_diagonal]
    simp only [generatedSixthAxisMatrix, ite_true]
  · rw [generatedSixth_matrix_off_diagonal i j hij]
    simp only [generatedSixthAxisMatrix, hij, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
