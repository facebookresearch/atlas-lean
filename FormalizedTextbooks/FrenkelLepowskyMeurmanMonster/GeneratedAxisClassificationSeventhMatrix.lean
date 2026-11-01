/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMiddlePairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhDiagonal

/-! Every coordinate of the actual seventh-axis matrix is fixed by original triality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The sparse matrix of the genuine exterior-triality image, without a spectral hypothesis. -/
def generatedSeventhAxisMatrix (i j : Fin 24) : ℝ :=
  if i = j then
    if i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 18 then 17 / 32 else 9 / 32
  else
    generatedSeventhMiddlePairValue 0 (if i < j then i else j) (if i < j then j else i) / 2

/-- The actual off-diagonal matrix coordinates are the complete sparse pair table. -/
theorem generatedSeventh_matrix_off_diagonal (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode generatedSeventhAxis).1 i j =
      generatedSeventhMiddlePairValue 0 (if i < j then i else j)
        (if i < j then j else i) / 2 := by
  rw [generatedSeventhAxis_local_expression,
    generatedFourth_triality_matrix_off_diagonal _ i j hij,
    generatedSeventh_middle_pair_coordinate, generatedSeventh_middle_pair_coordinate,
    griessPairIndex_coordinates]
  split_ifs <;> simp [generatedSeventhMiddlePairValue]

/-- The full original matrix watermark is unconditional for this literal generated word. -/
theorem generatedSeventh_axis_matrix :
    (griessConwayEncode generatedSeventhAxis).1 = generatedSeventhAxisMatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [generatedSeventh_matrix_diagonal]
    simp only [generatedSeventhAxisMatrix, ite_true]
  · rw [generatedSeventh_matrix_off_diagonal i j hij]
    simp only [generatedSeventhAxisMatrix, hij, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
