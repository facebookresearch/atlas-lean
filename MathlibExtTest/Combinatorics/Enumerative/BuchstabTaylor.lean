/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BuchstabTaylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Tests for the Buchstab coefficient recursion

At the first transition the constant term has a logarithmic closed form. The linear
coefficient uses the initial row's constant term.
-/

namespace MetaMathlibExt.BuchstabTaylor

variable (ω : ℝ → ℝ) (h₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
  (h₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
  (c : ℕ → ℕ → ℝ)
  (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
    HasSum (fun i ↦ c n i * z ^ i) (ω (n + (1 + z) / 2)))

example : c 2 0 = 2 * (1 + Real.log (3 / 2)) / 5 := by
  have h := buchstab_taylor_coeff_recursion ω h₁ h₂ c hc
  have hgeom := (hasSum_geometric_of_abs_lt_one (by norm_num : |(-1 / 3 : ℝ)| < 1)).mul_left
    (8 / 3)
  have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one (by norm_num : |(1 / 3 : ℝ)| < 1)).mul_left 2
  have hsum : HasSum (fun i : ℕ ↦ c 1 i * (4 + (-1 : ℝ) ^ i / (i + 1)))
      (2 + 2 * Real.log (3 / 2)) := by
    convert (hgeom.add hlog).congr_fun (g := fun i : ℕ ↦ c 1 i * (4 + (-1 : ℝ) ^ i / (i + 1)))
      ?_ using 1
    · rw [← Real.log_inv]
      norm_num
    · intro i
      have hsign : (-1 / 3 : ℝ) ^ i * (-1) ^ i = (1 / 3 : ℝ) ^ i := by
        rw [← mul_pow]
        norm_num
      rw [h.1 i, mul_add, mul_div_assoc', mul_assoc _ _ ((-1 : ℝ) ^ i), hsign, pow_succ]
      ring
  have hconst := h.2.1 1 le_rfl
  norm_num at hconst
  rw [hconst, hsum.tsum_eq]
  ring

example : c 2 1 = (2 / 3 - c 2 0) / 5 := by
  have h := buchstab_taylor_coeff_recursion ω h₁ h₂ c hc
  have hlinear := h.2.2 1 le_rfl 1 le_rfl
  norm_num [h.1 0] at hlinear
  exact hlinear

end MetaMathlibExt.BuchstabTaylor
