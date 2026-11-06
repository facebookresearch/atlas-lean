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

For `z₁, z₂` in the slit plane, `Log (z₁ z₂) = Log z₁ + Log z₂ + 2πin` with `n ∈ {-1, 0, 1}`, and
`n = 0` when `-π < Arg z₁ + Arg z₂ < π`
(`Complex.exists_log_mul_eq_add_log_add_int_mul_two_pi_I`, the book's Theorem 3 of Lecture 2). The
same holds for all nonzero `z₁, z₂`
(`Complex.exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero`).

Mathlib characterizes the case `n = 0` exactly: `Complex.log_mul_eq_add_log_iff` says it holds iff
`Arg z₁ + Arg z₂ ∈ (-π, π]`.

Rubric-guided revision of v1 ComplexVariables target 4 (`Complex.log_mul_eq_add_log_add_int` in
`v1/Atlas/ComplexVariables/code/Lecture2.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 56–88). The archived statement proved
`n ∈ {-1, 0, 1}` but dropped the book's clause that `n = 0` when `-π < Arg z₁ + Arg z₂ < π`, and
replaced the slit-plane hypotheses by `z ≠ 0`; the book's statement now has its own hypotheses, and
the `z ≠ 0` version is kept as the general form it follows from. The archived formalization and its
original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open scoped Real

namespace Complex

/-- For nonzero `z₁, z₂`, `log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I)` for an integer
`n ∈ {-1, 0, 1}`, and `n = 0` when `-π < arg z₁ + arg z₂ < π`. -/
public theorem exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero {z₁ z₂ : ℂ}
    (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    ∃ n : ℤ, log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) ∧ n ∈ ({-1, 0, 1} : Set ℤ) ∧
      (arg z₁ + arg z₂ ∈ Set.Ioo (-π) π → n = 0) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) := by
    rw [← exp_eq_exp_iff_exists_int, exp_add, exp_log (mul_ne_zero h₁ h₂), exp_log h₁,
      exp_log h₂]
  refine ⟨n, hn, ?_, fun hab ↦ ?_⟩
  · have harg : arg (z₁ * z₂) = arg z₁ + arg z₂ + n * (2 * π) := by
      simpa [log_im] using congr_arg im hn
    have hlt : (n : ℝ) < 2 := by
      nlinarith [Real.pi_pos, arg_le_pi (z₁ * z₂), neg_pi_lt_arg z₁, neg_pi_lt_arg z₂]
    have hgt : (-2 : ℝ) < n := by
      nlinarith [Real.pi_pos, neg_pi_lt_arg (z₁ * z₂), arg_le_pi z₁, arg_le_pi z₂]
    have hlt' : n < 2 := by exact_mod_cast hlt
    have hgt' : -2 < n := by exact_mod_cast hgt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rw [(log_mul_eq_add_log_iff h₁ h₂).2 (Set.Ioo_subset_Ioc_self hab), left_eq_add,
      mul_eq_zero, Int.cast_eq_zero] at hn
    exact hn.resolve_right two_pi_I_ne_zero

/-- **Logarithm of a product** (Theorem 3 of Lecture 2). For `z₁, z₂` in the slit plane,
`log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I)` for an integer `n ∈ {-1, 0, 1}`, and `n = 0`
when `-π < arg z₁ + arg z₂ < π`. -/
public theorem exists_log_mul_eq_add_log_add_int_mul_two_pi_I {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane)
    (hz₂ : z₂ ∈ slitPlane) :
    ∃ n : ℤ, log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) ∧ n ∈ ({-1, 0, 1} : Set ℤ) ∧
      (arg z₁ + arg z₂ ∈ Set.Ioo (-π) π → n = 0) :=
  exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero (slitPlane_ne_zero hz₁)
    (slitPlane_ne_zero hz₂)

end Complex
