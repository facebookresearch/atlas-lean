/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.LawOfSupply
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Tests for `MathlibExt.Economics.Producer.LawOfSupply`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Producer.LawOfSupply

open _root_.MathlibExt.Economics.Producer

/-- Test production set: three net-output vectors on two goods. -/
def testY : Set (Fin 2 → ℝ) := {![0, 0], ![1, -1], ![2, -3]}

/-- At prices `![3, 2]`, the plan `![1, -1]` (profit `1`) is the unique maximizer. -/
theorem test_max_p : IsProfitMax testY ![3, 2] ![1, -1] := by
  constructor
  · simp [testY]
  · intro y' hy
    simp only [testY, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- At prices `![4, 1]`, the plan `![2, -3]` (profit `5`) is the unique maximizer. -/
theorem test_max_p' : IsProfitMax testY ![4, 1] ![2, -3] := by
  constructor
  · simp [testY]
  · intro y' hy
    simp only [testY, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Numerical check: `(p - p') ⬝ᵥ (y - y') = 3` for the test prices and maximizers. -/
theorem test_dot_eq :
    (((![3, 2] : Fin 2 → ℝ) - ![4, 1]) ⬝ᵥ ((![1, -1] : Fin 2 → ℝ) - ![2, -3])) = 3 := by
  norm_num [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- The law of supply applied to the two test maximizers. -/
theorem test_law_of_supply :
    0 ≤ (((![3, 2] : Fin 2 → ℝ) - ![4, 1]) ⬝ᵥ ((![1, -1] : Fin 2 → ℝ) - ![2, -3])) :=
  test_max_p.law_of_supply test_max_p'

/-- At prices `![5, 2]`, the plan `![2, -3]` (profit `4`) is the unique maximizer. -/
theorem test_max_q' : IsProfitMax testY ![5, 2] ![2, -3] := by
  constructor
  · simp [testY]
  · intro y' hy
    simp only [testY, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Single-price law of supply: only the price of good `0` changes (`3 → 5`). -/
theorem test_single :
    0 ≤ (((![3, 2] : Fin 2 → ℝ) 0 - (![5, 2] : Fin 2 → ℝ) 0) *
      (((![1, -1] : Fin 2 → ℝ) 0 - (![2, -3] : Fin 2 → ℝ) 0))) := by
  have hp : ∀ j, j ≠ 0 → (![3, 2] : Fin 2 → ℝ) j = (![5, 2] : Fin 2 → ℝ) j := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · rfl
  exact test_max_p.law_of_supply_single test_max_q' 0 hp

/-- Numerical check: `(3 - 5) * (1 - 2) = 2` for the single-price test. -/
theorem test_single_eq :
    (((![3, 2] : Fin 2 → ℝ) 0 - (![5, 2] : Fin 2 → ℝ) 0) *
      (((![1, -1] : Fin 2 → ℝ) 0 - (![2, -3] : Fin 2 → ℝ) 0))) = 2 := by
  norm_num [Matrix.cons_val_zero]

end MathlibExtTest.Economics.Producer.LawOfSupply
