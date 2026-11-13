/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Inequality.Gini
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MathlibExtTest.Economics.Inequality.Gini

open MathlibExt.Economics.Inequality

theorem gini_one_two_three : gini ![1, 2, 3] = 2 / 9 := by
  unfold gini
  simp [Fin.sum_univ_three, Fintype.card_fin]
  norm_num

theorem gini_two_four_six : gini ![2, 4, 6] = 2 / 9 := by
  have h : (![2, 4, 6] : Fin 3 → ℝ) = (2 : ℝ) • ![1, 2, 3] := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul] <;> norm_num
  rw [h, gini_smul _ (show (0 : ℝ) < 2 by norm_num), gini_one_two_three]

theorem gini_const : gini (fun _ : Fin 3 => (5 : ℝ)) = 0 := by
  simp [gini]

theorem gini_neg_smul : gini ((-1 : ℝ) • ![1, 2, 3]) = -(2 / 9) := by
  unfold gini
  simp [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Fintype.card_fin]
  norm_num

example : gini ((-1 : ℝ) • ![1, 2, 3]) ≠ gini ![1, 2, 3] := by
  rw [gini_neg_smul, gini_one_two_three]
  norm_num

example : gini ((2 : ℝ) • ![1, 2, 3]) = gini ![1, 2, 3] := by
  have hx : (0 : ℝ) < ∑ i, (![1, 2, 3] : Fin 3 → ℝ) i := by
    simp [Fin.sum_univ_three]
    norm_num
  exact gini_smul_of_sum_pos _ hx (show (0 : ℝ) < 2 by norm_num)

end MathlibExtTest.Economics.Inequality.Gini