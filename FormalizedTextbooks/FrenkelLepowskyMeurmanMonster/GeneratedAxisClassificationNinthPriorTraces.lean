/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTrace

/-! Exact prior prototype traces needed for genuine ninth local-orbit separation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

set_option maxHeartbeats 4000000 in
-- Evaluate the 576 genuine sixth matrix products from its checked sparse source table.
/-- The actual sixth prototype has matrix-square trace 497/128. -/
theorem generatedNinth_prior_sixth_trace :
    generatedFourthMatrixSquareTrace generatedSixthAxis = 497 / 128 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedSixth_axis_matrix]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, generatedSixthAxisMatrix,
    generatedSixthMiddlePairValue, Fin.sum_univ_succ]

set_option maxHeartbeats 4000000 in
-- Evaluate the 576 genuine seventh matrix products from its checked sparse source table.
/-- The actual seventh prototype has matrix-square trace 385/128. -/
theorem generatedNinth_prior_seventh_trace :
    generatedFourthMatrixSquareTrace generatedSeventhAxis = 385 / 128 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedSeventh_axis_matrix]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, generatedSeventhAxisMatrix,
    generatedSeventhMiddlePairValue, Fin.sum_univ_succ]

set_option maxHeartbeats 4000000 in
-- Evaluate the genuine eighth diagonal trace from its complete original coordinate formula.
/-- The actual eighth prototype has matrix-square trace 47/16. -/
theorem generatedNinth_prior_eighth_trace :
    generatedFourthMatrixSquareTrace generatedEighthAxis = 47 / 16 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedEighth_axis_matrix]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, generatedEighthAxisMatrix,
    Fin.sum_univ_succ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
