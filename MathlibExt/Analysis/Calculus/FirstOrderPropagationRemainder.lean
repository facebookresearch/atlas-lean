/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Nonlinear first-order propagation has an explicit remainder

If `f` is twice continuously differentiable and `|f''| ≤ M` everywhere,
then the first-order Taylor remainder satisfies
`|f (x₀ + h) - f x₀ - f' x₀ * h| ≤ (M / 2) * h ^ 2`.

## i. Overview

Taylor's theorem with the Lagrange remainder at order one gives
`ξ` between `x₀` and `x₀ + h` with
`f (x₀ + h) - (f x₀ + f' x₀ * h) = f'' ξ * h ^ 2 / 2`. Taking absolute
values and using `|f'' ξ| ≤ M` gives the bound. The hypothesis `0 ≤ M` is
kept for the statement's shape; it is not needed by the proof, since
`|f'' ξ| ≤ M` already forces `M ≥ 0`.

## ii. Key results

- `MathlibExt.Analysis.first_order_propagation_remainder_bound`: the
  first-order propagation remainder bound.

## iii. References

- `taylor_mean_remainder_lagrange_iteratedDeriv` (Mathlib).
-/

@[expose] public section

namespace MathlibExt.Analysis

set_option linter.unusedVariables false in
/-- Nonlinear first-order propagation has an explicit remainder under
smoothness: if `f` is twice continuously differentiable and
`|f''| ≤ M` everywhere, then the first-order Taylor remainder satisfies
`|f (x₀ + h) - f x₀ - f' x₀ * h| ≤ (M / 2) * h ^ 2`. -/
theorem first_order_propagation_remainder_bound {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ContDiff ℝ 2 f) (hderiv2 : ∀ x, |deriv (deriv f) x| ≤ M)
    (x₀ h : ℝ) :
    |f (x₀ + h) - f x₀ - deriv f x₀ * h| ≤ (M / 2) * h ^ 2 := by
  by_cases hh : h = 0
  · subst hh
    simp
  · have hx : x₀ ≠ x₀ + h := by
      intro heq
      apply hh
      linarith
    obtain ⟨ξ, _, hξeq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) (x := x₀ + h) (x₀ := x₀)
        hx hf.contDiffOn
    have hdiff : DifferentiableAt ℝ f x₀ :=
      (hf.differentiable (by simp)).differentiableAt
    have hud : UniqueDiffWithinAt ℝ (Set.uIcc x₀ (x₀ + h)) x₀ :=
      (uniqueDiffOn_uIcc hx).uniqueDiffWithinAt Set.left_mem_uIcc
    have hderivWithin : derivWithin f (Set.uIcc x₀ (x₀ + h)) x₀ = deriv f x₀ :=
      hdiff.derivWithin hud
    have hiter1 : iteratedDerivWithin (0 + 1) f (Set.uIcc x₀ (x₀ + h)) x₀
        = deriv f x₀ := by
      rw [show (0 + 1 : ℕ) = 1 from rfl, iteratedDerivWithin_one]
      exact hderivWithin
    have htaylor : taylorWithinEval f 1 (Set.uIcc x₀ (x₀ + h)) x₀ (x₀ + h)
        = f x₀ + deriv f x₀ * h := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ,
        taylor_within_zero_eval, hiter1]
      simp only [smul_eq_mul]
      congr 1
      simp
      ring
    have hiter2 : iteratedDeriv (1 + 1) f ξ = deriv (deriv f) ξ := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [htaylor, hiter2] at hξeq
    have hsub : (x₀ + h) - x₀ = h := by ring
    rw [hsub, show (1 + 1 : ℕ) = 2 from rfl, Nat.factorial_two] at hξeq
    norm_num at hξeq
    have hgoal : f (x₀ + h) - f x₀ - deriv f x₀ * h
        = f (x₀ + h) - (f x₀ + deriv f x₀ * h) := by ring
    rw [hgoal, hξeq]
    have hh2 : (0 : ℝ) ≤ h ^ 2 := sq_nonneg h
    have habs : |deriv (deriv f) ξ * h ^ 2 / 2|
        = |deriv (deriv f) ξ| * (h ^ 2) / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hh2,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    have hmul : |deriv (deriv f) ξ| * (h ^ 2) ≤ M * (h ^ 2) :=
      mul_le_mul_of_nonneg_right (hderiv2 ξ) hh2
    have hle : |deriv (deriv f) ξ| * (h ^ 2) / 2 ≤ M * (h ^ 2) / 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hmul
        (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))
    have heq : M * (h ^ 2) / 2 = (M / 2) * h ^ 2 := by ring
    rw [← heq]
    exact hle

end MathlibExt.Analysis
