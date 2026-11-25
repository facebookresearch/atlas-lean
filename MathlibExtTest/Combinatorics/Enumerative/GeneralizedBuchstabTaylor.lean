/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedBuchstabTaylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Tests for the generalized Buchstab coefficient recursion

Check the logarithmic constant term at the second midpoint and the first two
positive-degree coefficients across the transition to the third row.
-/

namespace MetaMathlibExt.GeneralizedBuchstabTaylorTests

variable (K : ℝ) (hK : 0 < K)
  (Ω : ℝ → ℝ) (h₁ : ∀ x ∈ Set.Ico (1 : ℝ) 2, Ω x = 1)
  (h₂ : ∀ x : ℝ, 2 ≤ x → Ω x = 1 + K * ∫ u in (2 : ℝ)..x, Ω (u - 1) / (u - 1))
  (c : ℕ → ℕ → ℝ)
  (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
    HasSum (fun i ↦ c n i * z ^ i) (Ω (n + (1 + z) / 2)))

include hK h₁ h₂ hc

private theorem second_constant : c 2 0 = 1 + K * Real.log (3 / 2) := by
  have h := generalized_buchstab_taylor_coeff_recursion K hK Ω h₁ h₂ c hc
  have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one (by norm_num : |(-1 / 2 : ℝ)| < 1)).neg
  have hsum : HasSum (fun i : ℕ ↦ (-1 : ℝ) ^ i / (((i : ℝ) + 1) * 2 ^ (i + 1)))
      (Real.log (3 / 2)) := by
    convert hlog using 1
    · ext i
      rw [div_pow, pow_succ (-1 : ℝ)]
      field_simp
    · norm_num
  rw [h.2.2.1, hsum.tsum_eq]

private theorem second_linear : c 2 1 = K / 3 := by
  have h := generalized_buchstab_taylor_coeff_recursion K hK Ω h₁ h₂ c hc
  have hgeom := (hasSum_geometric_of_abs_lt_one (by norm_num : |(-1 / 2 : ℝ)| < 1)).div_const 2
  have hsum : HasSum (fun j : ℕ ↦ (-1 : ℝ) ^ (j + 1 - 1) * ((j + 1).choose 1 : ℝ) /
      (((j : ℝ) + 1) * 2 ^ (j + 1))) (1 / 3) := by
    convert hgeom using 1
    · ext j
      rw [Nat.add_sub_cancel, Nat.choose_one_right, Nat.cast_add, Nat.cast_one,
        div_pow, pow_succ (2 : ℝ)]
      field_simp
    · norm_num
  rw [h.2.2.2.1 1 le_rfl]
  simp only [Nat.cast_one, hsum.tsum_eq]
  ring

example : c 3 2 = K * (K / 3 - (1 + K * Real.log (3 / 2)) / 5) / 10 := by
  have h := generalized_buchstab_taylor_coeff_recursion K hK Ω h₁ h₂ c hc
  have hquad := h.2.2.2.2.2 3 (by decide) 2 (by decide)
  norm_num [Finset.sum_range_succ] at hquad
  rw [hquad, second_constant K hK Ω h₁ h₂ c hc, second_linear K hK Ω h₁ h₂ c hc]
  ring

end MetaMathlibExt.GeneralizedBuchstabTaylorTests
