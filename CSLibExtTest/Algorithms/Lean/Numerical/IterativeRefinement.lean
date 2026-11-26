/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.IterativeRefinement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter Cslib.Algorithms.Lean.Numerical

-- Exact residuals with half-size corrections give a geometric bound and zero limiting error.
example :
    (∀ i : ℕ, ‖(1 / 2 : ℝ) ^ i‖ ≤ (1 / 2 : ℝ) ^ i) ∧
    limsup (fun i : ℕ => ‖(1 / 2 : ℝ) ^ i‖) atTop ≤ 0 := by
  let x (i : ℕ) : ℝ := (1 / 2) ^ i
  let A := ContinuousLinearEquiv.refl ℝ ℝ
  have hres (i : ℕ) : ‖-x i - (0 - A (x i))‖ ≤ 0 := by simp [A]
  have hcorr (i : ℕ) : ‖-(x i / 2) - A.symm (-x i)‖ ≤ (1 / 2) * ‖A.symm (-x i)‖ := by
    simp only [A, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply]
    rw [show -(x i / 2) - -x i = (1 / 2) * x i by ring, norm_mul, norm_neg]
    rw [Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hupdate (i : ℕ) : x (i + 1) = x i + -(x i / 2) + 0 := by
    dsimp only [x]
    rw [pow_succ]
    ring
  have h := iterative_refinement_error_bound A 0 x (fun i => -x i) (fun i => -(x i / 2))
    (fun _ => 0) 0 (1 / 2) 0 (by norm_num) (by norm_num) hres hcorr (by simp) hupdate
  simpa only [A, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply, sub_zero,
    mul_zero, add_zero, zero_div, zero_add, x, pow_zero, norm_one, mul_one] using h.2

-- A persistently inaccurate residual permits a nonzero limiting error.
example : Filter.limsup (fun _ : ℕ => ‖(2 : ℝ)‖) Filter.atTop ≤ 2 := by
  let A := ContinuousLinearEquiv.refl ℝ ℝ
  have h := iterative_refinement_error_bound A 0 (fun _ => 2) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) 2 0 0 le_rfl (by norm_num)
    (by intro; norm_num [A]) (by simp) (by simp) (by simp)
  have hnorm : ‖A.symm.toContinuousLinearMap‖ = 1 := by
    change ‖ContinuousLinearMap.id ℝ ℝ‖ = 1
    exact ContinuousLinearMap.norm_id
  have hbound := h.2.2
  change limsup (fun _ : ℕ => ‖(2 : ℝ) - A.symm 0‖) atTop ≤
    ((1 + 0) * ‖A.symm.toContinuousLinearMap‖ * 2 + 0) / (1 - 0) at hbound
  simpa only [hnorm, map_zero, sub_zero, add_zero, one_mul, div_one] using hbound
