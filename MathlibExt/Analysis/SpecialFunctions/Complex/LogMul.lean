/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The principal logarithm of a product

For nonzero `z₁ z₂ : ℂ`, `Log (z₁ z₂) = Log z₁ + Log z₂ + 2πin` with `n ∈ {-1, 0, 1}`, and
`n = 0` when `|Arg z₁ + Arg z₂| < π` (`Complex.log_mul_eq_add_log_add_int`).

Mathlib characterizes the case `n = 0` exactly: `Complex.log_mul_eq_add_log_iff` says it holds iff
`Arg z₁ + Arg z₂ ∈ (-π, π]`. The integer form is the book's Theorem 3 of Lecture 2.

Code-derived port of `Complex.log_mul_eq_add_log_add_int` from
`v1/Atlas/ComplexVariables/code/Lecture2.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 56–88, which proved `n ∈ {-1, 0, 1}` but
dropped the book's clause that `n = 0` when `|Arg z₁ + Arg z₂| < π`; that clause is added here.
The archived formalization and its original license/provenance remain in `v1/` (the original
license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Real

namespace Complex

/-- For nonzero `z₁ z₂`, `Log (z₁ z₂) = Log z₁ + Log z₂ + 2πin` with `n ∈ {-1, 0, 1}`, and
`n = 0` when `|Arg z₁ + Arg z₂| < π`. -/
public theorem log_mul_eq_add_log_add_int {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    ∃ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) ∧
      log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) ∧
      (|arg z₁ + arg z₂| < π → n = 0) := by
  have h1 : exp (log (z₁ * z₂)) = exp (log z₁ + log z₂) := by
    rw [exp_log (mul_ne_zero hz₁ hz₂), exp_add, exp_log hz₁, exp_log hz₂]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp h1
  have him_n : arg (z₁ * z₂) = arg z₁ + arg z₂ + n * (2 * π) := by
    have := congr_arg im hn
    simp [log_im] at this
    linarith
  have hpi : (0 : ℝ) < π := pi_pos
  refine ⟨n, ?_, hn, fun hs => ?_⟩
  · have hn_bound : -3 * π < n * (2 * π) ∧ n * (2 * π) < 3 * π := by
      constructor <;> nlinarith [neg_pi_lt_arg (z₁ * z₂), arg_le_pi (z₁ * z₂),
        neg_pi_lt_arg z₁, neg_pi_lt_arg z₂, arg_le_pi z₁, arg_le_pi z₂]
    have hn_le : n ≤ 1 := by
      by_contra h
      have : (2 : ℝ) ≤ n := by exact_mod_cast (not_le.mp h)
      nlinarith
    have hn_ge : -1 ≤ n := by
      by_contra h
      have : (n : ℝ) ≤ -2 := by exact_mod_cast (show n ≤ -2 by omega)
      nlinarith
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rw [abs_lt] at hs
    have hlt : (n : ℝ) < 1 := by nlinarith [arg_le_pi (z₁ * z₂)]
    have hgt : -1 < (n : ℝ) := by nlinarith [neg_pi_lt_arg (z₁ * z₂)]
    have : n < 1 := by exact_mod_cast hlt
    have : -1 < n := by exact_mod_cast hgt
    omega

end Complex
