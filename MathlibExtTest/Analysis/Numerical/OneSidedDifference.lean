/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Numerical.OneSidedDifference
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

open Set MetaMathlibExt

private theorem square_contDiff : ContDiff ℝ 2 (fun t : ℝ ↦ t ^ 2) :=
  contDiff_id.pow 2

private theorem deriv_square : deriv (fun t : ℝ ↦ t ^ 2) = fun t ↦ 2 * t := by
  funext t
  simp

private theorem iteratedDeriv_two_square (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ ↦ s ^ 2) t = 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_square,
    deriv_const_mul_id]

-- The forward quotient at `1` is `3`, so the nonzero remainder is subtracted.
example : ∃ ξ ∈ Ioo (1 : ℝ) 2,
    (2 : ℝ) = 3 - 1 / 2 * iteratedDeriv 2 (fun t : ℝ ↦ t ^ 2) ξ := by
  have hlt : (1 : ℝ) < 1 + 1 := by norm_num
  have hx := square_contDiff.differentiable (by decide) (1 : ℝ)
  have hWithin := hx.derivWithin (uniqueDiffOn_uIcc hlt.ne 1 left_mem_uIcc)
  obtain ⟨ξ, hξ, heq⟩ := derivWithin_eq_oneSidedDifference_sub_remainder
    (f := fun t : ℝ ↦ t ^ 2) (x := 1) (h := 1) (by norm_num) square_contDiff.contDiffOn
  rw [uIoo_of_lt hlt] at hξ
  rw [hWithin, deriv_square] at heq
  norm_num at hξ heq
  exact ⟨ξ, hξ, heq⟩

-- The backward quotient at `1` is `1`. With step `-1` the same signed formula adds the correction.
example : ∃ ξ ∈ Ioo (0 : ℝ) 1,
    (2 : ℝ) = 1 + 1 / 2 * iteratedDeriv 2 (fun t : ℝ ↦ t ^ 2) ξ := by
  have hgt : (1 : ℝ) + (-1) < 1 := by norm_num
  have hx := square_contDiff.differentiable (by decide) (1 : ℝ)
  obtain ⟨ξ, hξ, heq⟩ := deriv_eq_oneSidedDifference_sub_remainder
    (x := 1) (h := -1) (by norm_num) square_contDiff.contDiffOn hx
  rw [uIoo_of_gt hgt] at hξ
  norm_num [deriv_square, sub_eq_add_neg] at hξ heq
  exact ⟨ξ, hξ, heq⟩

-- The bound is attained for the square function and the negative step.
example : |(((1 : ℝ) + (-1)) ^ 2 - 1 ^ 2) / (-1) -
    derivWithin (fun t : ℝ ↦ t ^ 2) (uIcc 1 (1 + (-1))) 1| ≤ 1 := by
  have hBound := abs_oneSidedDifference_sub_derivWithin_le
    (f := fun t : ℝ ↦ t ^ 2) (x := 1) (h := -1) (M := 2) (by norm_num)
    square_contDiff.contDiffOn (fun ξ _ ↦ by rw [iteratedDeriv_two_square]; norm_num)
  norm_num at hBound ⊢
  exact hBound

-- The absolute value function has the interval derivative `1` at `0` on `[0, 1]`.
example : ∃ ξ ∈ Ioo (0 : ℝ) 1,
    (1 : ℝ) = 1 - 1 / 2 * iteratedDeriv 2 (abs : ℝ → ℝ) ξ := by
  have hlt : (0 : ℝ) < 0 + 1 := by norm_num
  have hOn : EqOn (abs : ℝ → ℝ) id (uIcc 0 (0 + 1)) := by
    rw [uIcc_of_lt hlt]
    intro t ht
    exact abs_of_nonneg ht.1
  have hf : ContDiffOn ℝ 2 (abs : ℝ → ℝ) (uIcc 0 (0 + 1)) :=
    contDiff_id.contDiffOn.congr hOn
  have hx : derivWithin (abs : ℝ → ℝ) (uIcc 0 (0 + 1)) 0 = 1 := by
    rw [derivWithin_congr hOn (hOn left_mem_uIcc)]
    exact derivWithin_id 0 _ (uniqueDiffOn_uIcc hlt.ne 0 left_mem_uIcc)
  obtain ⟨ξ, hξ, heq⟩ := derivWithin_eq_oneSidedDifference_sub_remainder (by norm_num) hf
  rw [uIoo_of_lt hlt] at hξ
  rw [hx] at heq
  norm_num at hξ heq
  exact ⟨ξ, hξ, heq⟩
