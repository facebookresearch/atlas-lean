/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.OddPowerSumKnuth

/-! # Tests for the odd Faulhaber expansion -/

open Finset MetaMathlibExt
open MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

private theorem arrayR_one_one : (arrayR 1 1 : ℚ) = 1 := by
  rw [arrayR_eq_closedForm 1 1 le_rfl le_rfl,
    show (univ.filter fun b : Fin 1 → Fin 2 =>
      (∑ r, (r.val + 1) * (b r).val) = 1 ∧ (∑ r, (b r).val) = 1) = {![1]} by decide]
  norm_num [Nat.multinomial, Nat.factorial]

private theorem arrayR_two_one : (arrayR 2 1 : ℚ) = 1 := by
  rw [arrayR_eq_closedForm 2 1 le_rfl (by decide),
    show (univ.filter fun b : Fin 2 → Fin 3 =>
      (∑ r, (r.val + 1) * (b r).val) = 2 ∧ (∑ r, (b r).val) = 1) = {![0, 1]} by decide]
  norm_num [Fin.prod_univ_two, Nat.multinomial, Nat.factorial]

private theorem arrayR_two_two : (arrayR 2 2 : ℚ) = 12 := by
  rw [arrayR_eq_closedForm 2 2 (by decide) le_rfl,
    show (univ.filter fun b : Fin 2 → Fin 3 =>
      (∑ r, (r.val + 1) * (b r).val) = 2 ∧ (∑ r, (b r).val) = 2) = {![2, 0]} by decide]
  norm_num [Fin.prod_univ_two, Nat.multinomial, Nat.factorial]

private theorem arrayR_three_one : (arrayR 3 1 : ℚ) = 1 := by
  rw [arrayR_eq_closedForm 3 1 le_rfl (by decide),
    show (univ.filter fun b : Fin 3 → Fin 4 =>
      (∑ r, (r.val + 1) * (b r).val) = 3 ∧ (∑ r, (b r).val) = 1) = {![0, 0, 1]} by decide]
  norm_num [Fin.prod_univ_three, Nat.multinomial, Nat.factorial]

private theorem arrayR_three_two : (arrayR 3 2 : ℚ) = 60 := by
  rw [arrayR_eq_closedForm 3 2 (by decide) (by decide),
    show (univ.filter fun b : Fin 3 → Fin 4 =>
      (∑ r, (r.val + 1) * (b r).val) = 3 ∧ (∑ r, (b r).val) = 2) = {![1, 1, 0]} by decide]
  norm_num [Fin.prod_univ_three, Nat.multinomial, Nat.factorial]

private theorem arrayR_three_three : (arrayR 3 3 : ℚ) = 360 := by
  rw [arrayR_eq_closedForm 3 3 (by decide) le_rfl,
    show (univ.filter fun b : Fin 3 → Fin 4 =>
      (∑ r, (r.val + 1) * (b r).val) = 3 ∧ (∑ r, (b r).val) = 3) = {![3, 0, 0]} by decide]
  norm_num [Fin.prod_univ_three, Nat.multinomial, Nat.factorial]

private theorem ls_two_one : legendreStirlingFirst 2 1 = -2 := by
  rw [legendreStirlingFirst_succ 1 0, legendreStirlingFirst_succ_zero 0,
    legendreStirlingFirst_diag 1]
  norm_num

private theorem ls_three_two : legendreStirlingFirst 3 2 = -8 := by
  rw [legendreStirlingFirst_succ 2 1, ls_two_one, legendreStirlingFirst_diag 2]
  norm_num

private theorem one_three_eq : powerSum 1 3 = 6 := by
  rw [show (1 : ℕ) = 2 * 1 - 1 by decide, powerSum_odd_eq_sum 1 le_rfl 3]
  norm_num [arrayR_one_one, Nat.choose]

-- The two signed terms give the nonzero binomial coefficient 5 for `m = 2, n = 3`.
example : ((3 + 2 : ℕ).choose (2 * 2) : ℚ) =
    (∑ r ∈ Icc 1 2, (legendreStirlingFirst 2 r : ℚ) * (2 * powerSum 1 3) ^ r) /
      ((2 * 2 : ℕ).factorial : ℚ) := by
  rw [show Icc 1 (2 : ℕ) = {1, 2} by decide]
  norm_num [one_three_eq, ls_two_one, legendreStirlingFirst_diag, Nat.choose, Nat.factorial]

-- The first cancellation has two nonzero terms, `1/2` and `-1/2`.
example : (∑ m ∈ Icc 1 2, (1 / (((2 * m).factorial : ℚ) * m)) *
    (arrayR 2 m : ℚ) * (legendreStirlingFirst m 1 : ℚ)) = 0 := by
  rw [show Icc 1 (2 : ℕ) = {1, 2} by decide]
  norm_num [arrayR_two_one, arrayR_two_two, ls_two_one, legendreStirlingFirst_diag, Nat.factorial]

-- The empty endpoint and the least exponent satisfy the same cubic identity.
example : powerSum 3 0 = (powerSum 1 0) ^ 2 * faulhaberC 1 1 := by
  have h (k : ℕ) (hk : 1 ≤ k) : powerSum (2 * k - 1) 0 = 0 := by
    rw [powerSum_odd_eq_sum k hk 0]
    apply sum_eq_zero
    intro m hm
    have hm₁ := (mem_Icc.mp hm).1
    simp [Nat.choose_eq_zero_of_lt (show m < 2 * m by omega)]
  rw [show powerSum 3 0 = 0 from h 2 (by decide), show powerSum 1 0 = 0 from h 1 le_rfl]
  simp

-- The cubic form has coefficient 1, giving 36 at n = 3.
example : powerSum 3 3 = 36 ∧ (powerSum 1 3) ^ 2 * faulhaberC 1 1 = 36 := by
  constructor
  · rw [show (3 : ℕ) = 2 * 2 - 1 by decide, powerSum_odd_eq_sum 2 (by decide) 3,
      show Icc 1 (2 : ℕ) = {1, 2} by decide]
    norm_num [arrayR_two_one, arrayR_two_two, Nat.choose]
  · rw [faulhaberC_eq_sum_succ]
    norm_num [one_three_eq, arrayR_two_two, legendreStirlingFirst_diag, Nat.factorial]

-- Compute both fifth-power coefficients before evaluating the expansion.
private theorem c_two_one : faulhaberC 2 1 = -1 / 3 := by
  rw [faulhaberC_eq_sum_succ, show Icc 2 (3 : ℕ) = {2, 3} by decide]
  norm_num [arrayR_three_two, arrayR_three_three, ls_three_two,
    legendreStirlingFirst_diag, Nat.factorial]

private theorem c_two_two : faulhaberC 2 2 = 4 / 3 := by
  rw [faulhaberC_eq_sum_succ]
  norm_num [arrayR_three_three, legendreStirlingFirst_diag, Nat.factorial]

-- At n = 3 the fifth-power sum and its Faulhaber expansion both evaluate to 276.
example : powerSum 5 3 = 276 ∧
    (powerSum 1 3) ^ 2 * (faulhaberC 2 1 + faulhaberC 2 2 * powerSum 1 3) = 276 := by
  constructor
  · rw [show (5 : ℕ) = 2 * 3 - 1 by decide, powerSum_odd_eq_sum 3 (by decide) 3,
      show Icc 1 (3 : ℕ) = {1, 2, 3} by decide]
    norm_num [arrayR_three_one, arrayR_three_two, arrayR_three_three, Nat.choose]
  · norm_num [one_three_eq, c_two_one, c_two_two]
