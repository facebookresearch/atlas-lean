/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Error of the one-sided difference quotient

The degree-one Taylor expansion gives an exact error formula for the one-sided difference
quotient, for either sign of the nonzero step. At the expansion endpoint, interval regularity
alone gives a derivative within the interval; at the strictly interior remainder point one can
use the ordinary second derivative.

## References

* D. Levy, *Introduction to Numerical Analysis*, 4 January 2021, §5.1, (5.2)–(5.3),
  and §5.2, Example 5.1. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
-/

public section

open Set

namespace MetaMathlibExt

/-- Exact one-sided difference quotient formula with the degree-one Lagrange remainder.
The step `h` may have either sign. Only the derivative at `x` is taken within the closed interval;
the ordinary second derivative is evaluated at a point strictly between `x` and `x + h`. -/
theorem exists_derivWithin_eq_oneSidedDifference_sub_remainder {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0)
    (hf : ContDiffOn ℝ 2 f (uIcc x (x + h))) :
    ∃ ξ ∈ uIoo x (x + h), derivWithin f (uIcc x (x + h)) x =
      (f (x + h) - f x) / h - h / 2 * iteratedDeriv 2 f ξ := by
  have hne : x ≠ x + h := fun heq ↦ hh (add_left_cancel (heq.symm.trans (add_zero x).symm))
  obtain ⟨ξ, hξ, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf
  rw [taylorWithinEval_succ f 0] at hTaylor
  norm_num [taylor_within_zero_eval, iteratedDerivWithin_one, smul_eq_mul, Nat.factorial]
    at hTaylor
  refine ⟨ξ, hξ, eq_sub_iff_add_eq.mpr ((eq_div_iff hh).mpr ?_)⟩
  linear_combination -hTaylor

/-- If `f` is differentiable at the expansion point in the ambient real line, the exact formula
for the one-sided difference quotient uses the ordinary derivative there. -/
theorem exists_deriv_eq_oneSidedDifference_sub_remainder {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0)
    (hf : ContDiffOn ℝ 2 f (uIcc x (x + h))) (hx : DifferentiableAt ℝ f x) :
    ∃ ξ ∈ uIoo x (x + h), deriv f x =
      (f (x + h) - f x) / h - h / 2 * iteratedDeriv 2 f ξ := by
  have hne : x ≠ x + h := fun heq ↦ hh (add_left_cancel (heq.symm.trans (add_zero x).symm))
  simpa only [hx.derivWithin (uniqueDiffOn_uIcc hne x left_mem_uIcc)] using
    exists_derivWithin_eq_oneSidedDifference_sub_remainder hh hf

/-- An absolute bound `M` on the second derivative in the open interval bounds the error of the
one-sided difference quotient by `|h| / 2 * M`. -/
theorem abs_oneSidedDifference_sub_derivWithin_le {f : ℝ → ℝ} {x h M : ℝ} (hh : h ≠ 0)
    (hf : ContDiffOn ℝ 2 f (uIcc x (x + h)))
    (hM : ∀ ξ ∈ uIoo x (x + h), |iteratedDeriv 2 f ξ| ≤ M) :
    |(f (x + h) - f x) / h - derivWithin f (uIcc x (x + h)) x| ≤ |h| / 2 * M := by
  obtain ⟨ξ, hξ, hDeriv⟩ := exists_derivWithin_eq_oneSidedDifference_sub_remainder hh hf
  rw [hDeriv, sub_sub_cancel, abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (hM ξ hξ) (div_nonneg (abs_nonneg h) (by norm_num))

end MetaMathlibExt
