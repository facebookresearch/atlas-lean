/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequality

/-!
# Tests for `MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequality`

* The inequality `‖f‖₂² ≤ 2 ‖x f‖₂ ‖f'‖₂` on an arbitrary real Schwartz function.
* The zero function: both sides vanish, so equality holds.
* A nonzero real Schwartz function has positive mass `∫ ‖f x‖²`, so the inequality forces both
  the weighted second moment `∫ ‖x * f x‖²` and the derivative energy `∫ ‖f' x‖²` to be positive.
-/

open MeasureTheory
open scoped SchwartzMap
open MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted

namespace MathlibExtTest.Analysis.Fourier.SchwartzWeightedL2DerivInequality

/-- The inequality on an arbitrary real Schwartz function, in the stated form. -/
example (f : 𝓢(ℝ, ℝ)) :
    (∫ x : ℝ, ‖f x‖ ^ 2) ≤
      2 * Real.sqrt (∫ x : ℝ, ‖x * f x‖ ^ 2) *
        Real.sqrt (∫ x : ℝ, ‖deriv (fun y : ℝ => f y) x‖ ^ 2) :=
  integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq f

/-- For the zero function both sides vanish, so the inequality is an equality. -/
example :
    (∫ x : ℝ, ‖(0 : 𝓢(ℝ, ℝ)) x‖ ^ 2) = 0 ∧
      2 * Real.sqrt (∫ x : ℝ, ‖x * (0 : 𝓢(ℝ, ℝ)) x‖ ^ 2) *
        Real.sqrt (∫ x : ℝ, ‖deriv (fun y : ℝ => (0 : 𝓢(ℝ, ℝ)) y) x‖ ^ 2) = 0 := by
  simp

/-- A nonzero real Schwartz function has positive weighted second moment and positive derivative
energy: its mass `∫ ‖f x‖²` is positive and at most twice the product of their square roots. -/
example (f : 𝓢(ℝ, ℝ)) (hf : f ≠ 0) :
    0 < ∫ x : ℝ, ‖x * f x‖ ^ 2 ∧ 0 < ∫ x : ℝ, ‖deriv (fun y : ℝ => f y) x‖ ^ 2 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 :=
    not_forall.1 fun h => hf (SchwartzMap.ext fun x => by simpa using h x)
  have hint : Integrable (fun x => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).1 (f.memLp 2)
  have hmass : 0 < ∫ x : ℝ, ‖f x‖ ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero (x := x₀) (by fun_prop) hint
      (fun x => by positivity) (by simpa using hx₀)
  have hpos := hmass.trans_le
    (integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq f)
  constructor
  · by_contra hX
    rw [Real.sqrt_eq_zero'.2 (not_lt.1 hX)] at hpos
    simp at hpos
  · by_contra hD
    rw [Real.sqrt_eq_zero'.2 (not_lt.1 hD)] at hpos
    simp at hpos

end MathlibExtTest.Analysis.Fourier.SchwartzWeightedL2DerivInequality
