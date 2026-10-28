/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTraceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTrace

/-! An actual local invariant distinguishes this original third-triality prototype. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine ninth matrix-square trace is eleven quarters. -/
theorem generatedNinth_matrix_square_trace :
    generatedFourthMatrixSquareTrace generatedNinthAxis = 11 / 4 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedNinth_axis_matrix]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, generatedNinthAxisMatrix]
  have hc : (∑ i : Fin 24, ∑ j : Fin 24,
      (generatedNinthMatrixNumerator i j : ℝ) *
        (generatedNinthMatrixNumerator j i : ℝ)) = 2816 := by
    exact_mod_cast generatedNinth_matrix_numerator_square_trace
  calc
    _ = (∑ i : Fin 24, ∑ j : Fin 24,
        (generatedNinthMatrixNumerator i j : ℝ) *
          (generatedNinthMatrixNumerator j i : ℝ)) / 1024 := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hc]; norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
