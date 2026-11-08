/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.PolynomialDecayMemLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tests for polynomial decay implying `L^p` membership

* The concrete decay function `x ↦ (1 + |x|) ^ (-2)` lies in `L^p (ℝ)` for every
  `1 ≤ p`, and its `L^2` norm is finite.
* A scaled decay function with `C = 3`, `q = 3` lies in `L^p (ℝ)` for every `1 ≤ p`.
* Counterexample to the `≥` form of the decay hypothesis: the constant function `1`
  satisfies `‖1‖ ≥ 1 * (1 + |x|) ^ (-2)` everywhere, but `1 ∉ L^2 (ℝ)`, so a lower
  decay bound does not imply `L^p` membership.
-/

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.Function.PolynomialDecay

namespace MathlibExtTest.MeasureTheory.Function.PolynomialDecayMemLpTests

/-- The concrete decay function lies in `L^p (ℝ)` for every `1 ≤ p`. -/
example {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) p volume := by
  apply memLp_of_polynomial_decay (C := 1) (q := 2) ?_ (by norm_num) (by norm_num) ?_ hp
  · apply Measurable.aestronglyMeasurable
    measurability
  · intro x
    simp

/-- A scaled decay function with `C = 3`, `q = 3` lies in `L^p (ℝ)` for every `1 ≤ p`. -/
example {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp (fun x : ℝ => 3 * (1 + |x|) ^ (-3 : ℝ)) p volume := by
  apply memLp_of_polynomial_decay (C := 3) (q := 3) ?_ (by norm_num) (by norm_num) ?_ hp
  · apply Measurable.aestronglyMeasurable
    measurability
  · intro x
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |x|) _)]

/-- The `L^2` norm of the concrete decay function is finite. -/
example : eLpNorm (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) 2 volume < ⊤ := by
  have h : MemLp (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) 2 volume := by
    apply memLp_of_polynomial_decay (C := 1) (q := 2) ?_ (by norm_num) (by norm_num) ?_
      (by norm_num)
    · apply Measurable.aestronglyMeasurable
      measurability
    · intro x
      simp
  exact h.eLpNorm_lt_top

/-- Increasing the value at a single null-set point preserves the decay conclusion.
The value at `0` is `2`, so the bound with `C = 1` holds only almost everywhere. -/
example {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp (fun x : ℝ => if x = 0 then (2 : ℝ) else (1 + |x|) ^ (-2 : ℝ))
      p volume := by
  apply memLp_of_polynomial_decay_ae (C := 1) (q := 2) ?_
    (by norm_num) (by norm_num) ?_ hp
  · apply Measurable.aestronglyMeasurable
    have hd : Measurable (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) := by
      measurability
    exact Measurable.ite (p := fun x : ℝ => x = 0) (f := fun _ : ℝ => (2 : ℝ))
        (g := fun x : ℝ => (1 + |x|) ^ (-2 : ℝ))
        (by simp) measurable_const hd
  · have hae : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      simp [ae_iff]
    filter_upwards [hae] with x hx
    simp [hx]

/-- Counterexample to the `≥` form of the decay hypothesis: the constant function `1`
satisfies `‖1‖ ≥ 1 * (1 + |x|) ^ (-2)` everywhere, but `1 ∉ L^2 (ℝ)`. -/
example : ¬ MemLp (fun _ : ℝ => (1 : ℝ)) 2 volume := by
  rw [memLp_const_iff (by norm_num) (by norm_num)]
  rintro (h | h)
  · exact one_ne_zero h
  · rw [Real.volume_univ] at h
    exact lt_irrefl _ h

end MathlibExtTest.MeasureTheory.Function.PolynomialDecayMemLpTests
