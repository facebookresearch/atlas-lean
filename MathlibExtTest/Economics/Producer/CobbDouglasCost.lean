/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.CobbDouglasCost

@[expose] public section

/-! Tests for `MathlibExt.Economics.Producer.CobbDouglasCost`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Producer.CobbDouglasCost

open _root_.Economics.Producer

/-- Helper for the tests: `x ^ (1/2 : ℝ)` when `x = y ^ 2`. -/
private theorem test_rpow_half (x y : ℝ) (hy : 0 ≤ y) (h : y ^ 2 = x) : x ^ (1 / 2 : ℝ) = y := by
  rw [← Real.sqrt_eq_rpow, ← h, Real.sqrt_sq hy]

/-- Test: cost equals `8` for `A = 1`, `a = ![1/2, 1/2]`, `w = ![1, 4]`, `q = 2`. -/
theorem test_cost : cobbDouglasCost 1 ![1/2, 1/2] ![1, 4] 2 = 8 := by
  have w0 : ((![1, 4] : Fin 2 → ℝ) 0) = 1 := by simp
  have w1 : ((![1, 4] : Fin 2 → ℝ) 1) = 4 := by simp
  have a0 : ((![1/2, 1/2] : Fin 2 → ℝ) 0) = 1 / 2 := by simp
  have a1 : ((![1/2, 1/2] : Fin 2 → ℝ) 1) = 1 / 2 := by simp
  unfold cobbDouglasCost
  rw [Fin.prod_univ_two, w0, w1, a0, a1]
  rw [show (1:ℝ)/(1/2) = 2 by norm_num, show (4:ℝ)/(1/2) = 8 by norm_num,
    ← Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) ≤ 8 by norm_num),
    show (2:ℝ)*8 = 16 by norm_num,
    test_rpow_half 16 4 (show (0:ℝ) ≤ 4 by norm_num) (show (4:ℝ)^2 = 16 by norm_num)]
  norm_num

/-- Test: demands equal `![4, 1]` for the same values. -/
theorem test_demand : cobbDouglasDemand 1 ![1/2, 1/2] ![1, 4] 2 = ![4, 1] := by
  funext i
  fin_cases i
  · simp only [cobbDouglasDemand]
    rw [test_cost]
    simp
    norm_num
  · simp only [cobbDouglasDemand]
    rw [test_cost]
    simp
    norm_num

/-- Test: the demands produce exactly `q = 2`, via the general theorem. -/
theorem test_production : cobbDouglas 1 ![1/2, 1/2] ![4, 1] = 2 := by
  have ha : ∀ i : Fin 2, 0 < (((![1/2, 1/2] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hw : ∀ i : Fin 2, 0 < (((![1, 4] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hsum : (∑ i, (((![1/2, 1/2] : Fin 2 → ℝ)) i)) = 1 := by
    rw [Fin.sum_univ_two]
    simp
    norm_num
  have h := cobbDouglas_cobbDouglasDemand (ι := Fin 2) (A := 1)
    (a := ![1/2, 1/2]) (w := ![1, 4]) (q := 2)
    (by norm_num) ha hsum hw (by norm_num)
  rw [test_demand] at h
  exact h

/-- Test: the off-demand bundle `![8, 1/2]` produces exactly `q = 2`. -/
theorem test_production_alt : cobbDouglas 1 ![1/2, 1/2] ![8, 1/2] = 2 := by
  have x0 : ((![8, 1/2] : Fin 2 → ℝ) 0) = 8 := by simp
  have x1 : ((![8, 1/2] : Fin 2 → ℝ) 1) = 1 / 2 := by simp
  have a0 : ((![1/2, 1/2] : Fin 2 → ℝ) 0) = 1 / 2 := by simp
  have a1 : ((![1/2, 1/2] : Fin 2 → ℝ) 1) = 1 / 2 := by simp
  unfold cobbDouglas
  rw [Fin.prod_univ_two, x0, x1, a0, a1]
  rw [← Real.mul_rpow (show (0:ℝ) ≤ 8 by norm_num) (show (0:ℝ) ≤ 1 / 2 by norm_num),
    show (8:ℝ) * (1 / 2) = 4 by norm_num,
    test_rpow_half 4 2 (show (0:ℝ) ≤ 2 by norm_num) (show (2:ℝ) ^ 2 = 4 by norm_num)]
  norm_num

/-- Test: the off-demand bundle `![8, 1/2]` costs `10` at `w = ![1, 4]`. -/
theorem test_dotProduct_value : ((![1, 4] : Fin 2 → ℝ) ⬝ᵥ ![8, 1/2]) = 10 := by
  simp only [dotProduct, Fin.sum_univ_two]
  simp
  norm_num

/-- Test: `cobbDouglasCost_le_dotProduct` at `A = 1`, `a = ![1/2, 1/2]`, `w = ![1, 4]`,
`q = 2`, `x = ![8, 1/2]` (which produces `2` and costs `10 ≥ 8`). -/
theorem test_cost_le_dotProduct_example :
    cobbDouglasCost 1 ![1/2, 1/2] ![1, 4] 2 ≤ ((![1, 4] : Fin 2 → ℝ) ⬝ᵥ ![8, 1/2]) := by
  have ha : ∀ i : Fin 2, 0 < (((![1/2, 1/2] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hw : ∀ i : Fin 2, 0 < (((![1, 4] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hsum : (∑ i, (((![1/2, 1/2] : Fin 2 → ℝ)) i)) = 1 := by
    rw [Fin.sum_univ_two]
    simp
    norm_num
  have hx : ∀ i : Fin 2, 0 ≤ (((![8, 1/2] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hout : (2:ℝ) ≤ cobbDouglas 1 ![1/2, 1/2] ![8, 1/2] :=
    le_of_eq test_production_alt.symm
  exact cobbDouglasCost_le_dotProduct (ι := Fin 2) (A := 1)
    (a := ![1/2, 1/2]) (w := ![1, 4]) (x := ![8, 1/2]) (q := 2)
    (by norm_num) ha hsum hw hx hout

/-- Test: exact values `8 ≤ 10` via `cobbDouglasCost_le_dotProduct` and `test_cost`. -/
theorem test_cost_le_eight_ten : (8:ℝ) ≤ 10 := by
  have h := test_cost_le_dotProduct_example
  rw [test_cost, test_dotProduct_value] at h
  exact h

/-- Test: `isLeast_cobbDouglasCost` at the same values gives `IsLeast _ 8`. -/
theorem test_isLeast_value :
    IsLeast {c | ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧
      2 ≤ cobbDouglas 1 (![1/2, 1/2] : Fin 2 → ℝ) x ∧
      c = ((![1, 4] : Fin 2 → ℝ) ⬝ᵥ x)} 8 := by
  have ha : ∀ i : Fin 2, 0 < (((![1/2, 1/2] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hw : ∀ i : Fin 2, 0 < (((![1, 4] : Fin 2 → ℝ)) i) := by
    intro i
    fin_cases i <;> simp
  have hsum : (∑ i, (((![1/2, 1/2] : Fin 2 → ℝ)) i)) = 1 := by
    rw [Fin.sum_univ_two]
    simp
    norm_num
  have h := isLeast_cobbDouglasCost (ι := Fin 2) (A := 1)
    (a := ![1/2, 1/2]) (w := ![1, 4]) (q := 2)
    (by norm_num) ha hsum hw (by norm_num)
  rw [test_cost] at h
  exact h

/-- Test: `8` is a lower bound via `isLeast_cobbDouglasCost` (`.2`). -/
theorem test_isLeast_lowerBounds : (8:ℝ) ∈ lowerBounds
    {c | ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧
      2 ≤ cobbDouglas 1 (![1/2, 1/2] : Fin 2 → ℝ) x ∧
      c = ((![1, 4] : Fin 2 → ℝ) ⬝ᵥ x)} :=
  test_isLeast_value.2

/-- Test: `8` is attained via `isLeast_cobbDouglasCost` (`.1`). -/
theorem test_isLeast_mem : (8:ℝ) ∈
    {c | ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧
      2 ≤ cobbDouglas 1 (![1/2, 1/2] : Fin 2 → ℝ) x ∧
      c = ((![1, 4] : Fin 2 → ℝ) ⬝ᵥ x)} :=
  test_isLeast_value.1

end MathlibExtTest.Economics.Producer.CobbDouglasCost
