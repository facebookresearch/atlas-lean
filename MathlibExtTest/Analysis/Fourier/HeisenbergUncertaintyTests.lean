/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.HeisenbergUncertainty
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for Heisenberg's uncertainty principle

* The integration-by-parts identity and all three forms of the inequality
  on the zero function and on an arbitrary Schwartz function (application
  tests).
* A concrete nonzero test case: a smooth bump function, viewed as a real
  Schwartz function, has `(bumpSchwartzReal 0) = 1` and strictly positive
  `∫ (f x)²`, so Heisenberg's inequality for it is nontrivial; its
  complexification satisfies the Fourier and centered forms.
* `#print axioms` for `heisenberg_uncertainty_complex`: standard triple only.
-/

open MeasureTheory
open scoped SchwartzMap
open scoped Topology
open MathlibExt.Analysis.Fourier.HeisenbergUncertainty

namespace MathlibExtTest.Analysis.Fourier.HeisenbergUncertaintyTests

/-- A smooth bump function on `ℝ`, viewed as a real Schwartz function. -/
noncomputable def bumpSchwartzReal : 𝓢(ℝ, ℝ) :=
  (⟨1, 2, zero_lt_one, one_lt_two⟩ : ContDiffBump (0 : ℝ)).hasCompactSupport.toSchwartzMap
    (⟨1, 2, zero_lt_one, one_lt_two⟩ : ContDiffBump (0 : ℝ)).contDiff

theorem bumpSchwartzReal_apply_zero : bumpSchwartzReal 0 = 1 := by
  have h : (⟨1, 2, zero_lt_one, one_lt_two⟩ : ContDiffBump (0 : ℝ)) 0 = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self (by norm_num)
  exact h

/-- The bump Schwartz function has strictly positive `∫ (f x)²`. -/
theorem bumpSchwartzReal_integral_sq_pos : 0 < ∫ x, (bumpSchwartzReal x) ^ 2 := by
  have hcont : Continuous fun x => (bumpSchwartzReal x) ^ 2 :=
    bumpSchwartzReal.continuous.pow 2
  have h0 : (bumpSchwartzReal 0) ^ 2 = 1 := by
    rw [bumpSchwartzReal_apply_zero]
    norm_num
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), (1 : ℝ) / 2 < (bumpSchwartzReal x) ^ 2 :=
    hcont.continuousAt.eventually (Ioi_mem_nhds (by
      show (1 : ℝ) / 2 < (bumpSchwartzReal 0) ^ 2
      rw [h0]
      norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsupp : Metric.ball (0 : ℝ) δ
      ⊆ Function.support (fun x => (bumpSchwartzReal x) ^ 2) := by
    intro x hx
    rw [Function.mem_support]
    exact ne_of_gt (by linarith [hball x hx])
  have hmeas : 0 < volume (Function.support (fun x => (bumpSchwartzReal x) ^ 2)) := by
    calc 0 < volume (Metric.ball (0 : ℝ) δ) := by
          rw [Real.volume_ball]
          exact ENNReal.ofReal_pos.mpr (by linarith)
      _ ≤ volume (Function.support (fun x => (bumpSchwartzReal x) ^ 2)) :=
          measure_mono hsupp
  have hint : Integrable (fun x => (bumpSchwartzReal x) ^ 2) := by
    have hmeas : AEStronglyMeasurable (⇑bumpSchwartzReal) volume :=
      bumpSchwartzReal.continuous.aestronglyMeasurable
    have h := (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mp
      (SchwartzMap.memLp bumpSchwartzReal 2)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg _) hint).mpr hmeas

/-- Heisenberg's inequality on the zero function. -/
example : (∫ x, ‖((0 : 𝓢(ℝ, ℂ))) x‖ ^ 2) ^ 2
    ≤ 4 * (∫ x, x ^ 2 * ‖((0 : 𝓢(ℝ, ℂ))) x‖ ^ 2)
      * (∫ x, ‖deriv ((0 : 𝓢(ℝ, ℂ))) x‖ ^ 2) :=
  heisenberg_uncertainty_complex 0

/-- The integration-by-parts identity on an arbitrary real Schwartz function. -/
example (f : 𝓢(ℝ, ℝ)) :
    ∫ x, (f x) ^ 2 = -2 * ∫ x, x * (f x * deriv f x) :=
  schwartz_integral_sq_eq_neg_two_mul f

/-- The real Heisenberg inequality on an arbitrary real Schwartz function. -/
example (f : 𝓢(ℝ, ℝ)) :
    (∫ x, (f x) ^ 2) ^ 2
      ≤ 4 * (∫ x, x ^ 2 * (f x) ^ 2) * (∫ x, (deriv f x) ^ 2) :=
  heisenberg_uncertainty_real f

/-- The Fourier form on an arbitrary complex Schwartz function. -/
example (f : 𝓢(ℝ, ℂ)) :
    (∫ x, ‖f x‖ ^ 2) ^ 2 ≤ 16 * Real.pi ^ 2 * (∫ x, x ^ 2 * ‖f x‖ ^ 2)
      * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) :=
  heisenberg_uncertainty_fourier f

/-- The shifted form on an arbitrary complex Schwartz function and center. -/
example (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (∫ x, ‖f x‖ ^ 2) ^ 2
      ≤ 4 * (∫ x, (x - a) ^ 2 * ‖f x‖ ^ 2) * (∫ x, ‖deriv f x‖ ^ 2) :=
  heisenberg_uncertainty_shifted f a

/-- Heisenberg's inequality for the bump function is nontrivial:
its `∫ (f x)²` is strictly positive. -/
example : (∫ x, (bumpSchwartzReal x) ^ 2) ^ 2
    ≤ 4 * (∫ x, x ^ 2 * (bumpSchwartzReal x) ^ 2)
      * (∫ x, (deriv bumpSchwartzReal x) ^ 2)
    ∧ 0 < ∫ x, (bumpSchwartzReal x) ^ 2 :=
  ⟨heisenberg_uncertainty_real bumpSchwartzReal, bumpSchwartzReal_integral_sq_pos⟩

/-- The complexification of the bump function satisfies the Fourier form. -/
example : (∫ x, ‖(SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartzReal) x‖ ^ 2) ^ 2
    ≤ 16 * Real.pi ^ 2
      * (∫ x, x ^ 2 * ‖(SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartzReal) x‖ ^ 2)
      * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier
          (SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartzReal) ξ‖ ^ 2) :=
  heisenberg_uncertainty_fourier _

/-- The complexification of the bump function satisfies the centered form. -/
example : (∫ x, ‖(SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartzReal) x‖ ^ 2) ^ 2
    ≤ 4 * (∫ x, (x - (∫ y, y * ‖(SchwartzMap.postcompCLM Complex.ofRealCLM
        bumpSchwartzReal) y‖ ^ 2) / (∫ z, ‖(SchwartzMap.postcompCLM Complex.ofRealCLM
        bumpSchwartzReal) z‖ ^ 2)) ^ 2
      * ‖(SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartzReal) x‖ ^ 2)
    * (∫ x, ‖deriv (SchwartzMap.postcompCLM Complex.ofRealCLM bumpSchwartzReal) x‖ ^ 2) :=
  heisenberg_uncertainty_centered _

#print axioms heisenberg_uncertainty_complex

end MathlibExtTest.Analysis.Fourier.HeisenbergUncertaintyTests
