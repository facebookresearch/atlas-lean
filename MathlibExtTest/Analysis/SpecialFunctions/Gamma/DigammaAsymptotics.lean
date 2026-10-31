/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics

/-!
# Tests for the digamma series and its sector asymptotics
-/

@[expose] public section

open Complex Filter

/-- The series at `z = 1` recovers Mathlib's `ψ(1) = -γ`. -/
example : digamma 1 = -Real.eulerMascheroniConstant := by
  rw [digamma_eq_tsum_sub_eulerMascheroniConstant (fun n h => by
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
  simp

/-- The series is consistent with Mathlib's `ψ(1/2) = -2 log 2 - γ`, at a point outside the
half-plane `Re z > 1` covered by `Complex.hasSum_digamma_series`. -/
example : (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 / 2))) = -2 * Complex.log 2 := by
  have h := digamma_eq_tsum_sub_eulerMascheroniConstant (z := 1 / 2) (fun n h => by
    have := congrArg re h
    norm_num at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  rw [digamma_one_half] at h
  linear_combination -h

/-- A point in the left half-plane that is not a pole. -/
example : digamma (-1 / 2) = (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + -1 / 2))) -
    Real.eulerMascheroniConstant :=
  digamma_eq_tsum_sub_eulerMascheroniConstant fun n h => by
    have := congrArg re h
    norm_num at this
    have h2 : (2 : ℝ) * n = 1 := by linarith
    have h3 : (2 * n : ℕ) = 1 := by exact_mod_cast h2
    omega

example (a b : ℂ) : Summable fun n : ℕ => 1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + b) :=
  summable_one_div_natCast_add_sub_one_div_natCast_add a b

example : Tendsto (fun N : ℕ => 1 / ((N : ℂ) + I)) atTop (nhds 0) :=
  tendsto_one_div_natCast_add_atTop I

/-- **Sector asymptotics** instantiated at `z = 1`. -/
example : ∃ C : ℝ, ‖digamma 1 - Complex.log 1‖ ≤ C / ‖(1 : ℂ)‖ := by
  obtain ⟨C, hC⟩ := exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  exact ⟨C, hC 1 one_ne_zero (by simp; positivity) (by simp; positivity)⟩

/-- Boundary probe: for `δ > π` the sector is empty and the statement is vacuous. -/
example : ∀ z : ℂ, z ≠ 0 → ¬ (-Real.pi + 5 ≤ arg z ∧ arg z ≤ Real.pi - 5) := by
  intro z _ ⟨h1, h2⟩
  linarith [Real.pi_le_four]
