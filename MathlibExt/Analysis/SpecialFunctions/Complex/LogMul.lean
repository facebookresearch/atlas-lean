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

The principal logarithm satisfies `Log (z₁ z₂) = Log z₁ + Log z₂ + 2πin` for an integer
`n ∈ {-1, 0, 1}`, with `n = 0` when `-π < Arg z₁ + Arg z₂ < π`, and in particular when `z₁ > 0`.

## Main results

* `Complex.exists_log_mul_eq_add_log_add_int_mul_two_pi_I`: Theorem 3 of Lecture 2 of the MIT
  notes cited below. The notes define `Arg w ∈ (-π, π)` and `Log w = log |w| + i Arg w` only on
  the slit plane `ℂ \ (-∞, 0]`, and the theorem and its proof take `z₁`, `z₂` and `z₁ z₂` all in
  it. The theorem assumes exactly that.
* `Complex.exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero`: the same conclusion for all
  nonzero `z₁, z₂`. It is a statement about Mathlib's total `Complex.log` and `Complex.arg`, which
  take `arg w ∈ (-π, π]`, so `arg w = π` and `log w = Real.log ‖w‖ + π * I` on the negative real
  axis. The slit-plane theorem follows from it.

Mathlib characterizes the case `n = 0` exactly: `Complex.log_mul_eq_add_log_iff` says it holds iff
`arg z₁ + arg z₂ ∈ (-π, π]`.

## References

* Zuoqin Wang, lecture notes for Sigurdur Helgason's *18.112 Functions of a Complex Variable*,
  MIT OpenCourseWare, Fall 2008, Lecture 2, Theorem 3 (printed page 5):
  <https://ocw.mit.edu/courses/18-112-functions-of-a-complex-variable-fall-2008/resources/lecture2/>

## Provenance

Rubric-guided revision of v1 ComplexVariables target 4 (`Complex.log_mul_eq_add_log_add_int` in
`v1/Atlas/ComplexVariables/code/Lecture2.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 56–88). The archived statement proved
`n ∈ {-1, 0, 1}` but dropped the source's clauses that `n = 0` when `-π < Arg z₁ + Arg z₂ < π`
and when `z₁ > 0`, and replaced the slit-plane hypotheses by `z ≠ 0`. The source's statement now
has its own hypotheses, and the `z ≠ 0` version is kept as the general form it follows from. The
archived formalization and its original license/provenance remain in `v1/` (the original license
text is `v1/LICENSE`).
-/

set_option autoImplicit false

open scoped Real ComplexOrder

namespace Complex

/-- For nonzero `z₁, z₂`, `log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I)` for an integer
`n ∈ {-1, 0, 1}`, and `n = 0` when `-π < arg z₁ + arg z₂ < π` or `z₁ > 0`.

Here `log` and `arg` are Mathlib's total functions, with `arg w ∈ (-π, π]`; on the negative real
axis `arg w = π`. With this convention, `n = 0` holds exactly when `arg z₁ + arg z₂ ∈ (-π, π]`
(`Complex.log_mul_eq_add_log_iff`). For example `n = 0` for `z₁ = z₂ = I`, whose product `-1` is
outside the slit plane. -/
public theorem exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero {z₁ z₂ : ℂ}
    (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    ∃ n : ℤ, log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) ∧ n ∈ ({-1, 0, 1} : Set ℤ) ∧
      (arg z₁ + arg z₂ ∈ Set.Ioo (-π) π → n = 0) ∧ (0 < z₁ → n = 0) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) := by
    rw [← exp_eq_exp_iff_exists_int, exp_add, exp_log (mul_ne_zero h₁ h₂), exp_log h₁,
      exp_log h₂]
  have hzero : arg z₁ + arg z₂ ∈ Set.Ioc (-π) π → n = 0 := fun hab ↦ by
    rw [(log_mul_eq_add_log_iff h₁ h₂).2 hab, left_eq_add, mul_eq_zero, Int.cast_eq_zero] at hn
    exact hn.resolve_right two_pi_I_ne_zero
  refine ⟨n, hn, ?_, fun hab ↦ hzero (Set.Ioo_subset_Ioc_self hab), fun hpos ↦ hzero ?_⟩
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
  · rw [arg_eq_zero_iff.2 ⟨(pos_iff.1 hpos).1.le, (pos_iff.1 hpos).2.symm⟩, zero_add]
    exact ⟨neg_pi_lt_arg z₂, arg_le_pi z₂⟩

/-- **Logarithm of a product** (Theorem 3 of Lecture 2 of the MIT 18.112 notes). For `z₁`, `z₂`
and `z₁ * z₂` in the slit plane, `log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I)` for an integer
`n ∈ {-1, 0, 1}`, and `n = 0` when `-π < arg z₁ + arg z₂ < π`; in particular `n = 0` when
`z₁ > 0`.

On the slit plane Mathlib's `log` and `arg` are the source's `Log` and `Arg`, with
`arg w ∈ (-π, π)`. The source defines `Log` only there, so it requires the product to lie there
too. The proof does not use that hypothesis, `_hz₁₂`:
`exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero` gives the same conclusion for all
nonzero `z₁, z₂` and Mathlib's total `log`. -/
public theorem exists_log_mul_eq_add_log_add_int_mul_two_pi_I {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ slitPlane)
    (hz₂ : z₂ ∈ slitPlane) (_hz₁₂ : z₁ * z₂ ∈ slitPlane) :
    ∃ n : ℤ, log (z₁ * z₂) = log z₁ + log z₂ + n * (2 * π * I) ∧ n ∈ ({-1, 0, 1} : Set ℤ) ∧
      (arg z₁ + arg z₂ ∈ Set.Ioo (-π) π → n = 0) ∧ (0 < z₁ → n = 0) :=
  exists_log_mul_eq_add_log_add_int_mul_two_pi_I_of_ne_zero (slitPlane_ne_zero hz₁)
    (slitPlane_ne_zero hz₂)

end Complex
