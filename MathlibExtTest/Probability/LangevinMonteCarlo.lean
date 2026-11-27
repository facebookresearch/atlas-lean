/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LangevinMonteCarlo
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Tests for the Langevin Monte Carlo step

* With `f = 0` a step from a point is the Gaussian `x + √(2h) ξ`.
* The quadratic `f θ = ‖θ‖² / 2` satisfies the strong-convexity and smoothness hypotheses of
  `WantedExt/Probability/LangevinMonteCarloWanted.lean` with `m = M = 1` (non-vacuity).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.LangevinMonteCarlo

namespace MathlibExtTest.LangevinMonteCarlo

local notation "R2" => EuclideanSpace ℝ (Fin 2)

theorem gradient_zero (x : R2) : gradient (fun _ : R2 => (0 : ℝ)) x = 0 := by
  have : HasGradientAt (fun _ : R2 => (0 : ℝ)) 0 x := by
    rw [hasGradientAt_iff_hasFDerivAt]; simpa using hasFDerivAt_const (0 : ℝ) x
  exact this.gradient

example (h : ℝ) (x : R2) :
    lmcStep (fun _ : R2 => (0 : ℝ)) h (Measure.dirac x) =
      (stdGaussian R2).map (fun ξ : R2 => x + Real.sqrt (2 * h) • ξ) := by
  have hg : gradient (fun _ : R2 => (0 : ℝ)) = 0 := funext gradient_zero
  rw [lmcStep_dirac (by rw [hg]; exact continuous_const)]
  simp [hg]

/-- `f θ = ‖θ‖² / 2`. -/
noncomputable def quadratic (θ : R2) : ℝ := (1 / 2 : ℝ) * ‖θ‖ ^ 2

theorem quadratic_gradient (θ : R2) : gradient quadratic θ = θ := by
  have : HasGradientAt quadratic θ θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    change HasFDerivAt (fun y : R2 => (1 / 2 : ℝ) * ‖y‖ ^ 2) ((InnerProductSpace.toDual ℝ R2) θ) θ
    convert! (hasStrictFDerivAt_norm_sq θ).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
    ext y
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  exact this.gradient

/-- Strong convexity with `m = 1`, in the form of Dalalyan's condition (1): equality holds. -/
example (θ θ' : R2) :
    1 / 2 * ‖θ - θ'‖ ^ 2 ≤
      quadratic θ - quadratic θ' - inner ℝ (gradient quadratic θ') (θ - θ') := by
  rw [quadratic_gradient]
  simp only [quadratic]
  rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  nlinarith [sq_nonneg ‖θ'‖]

/-- Smoothness with `M = 1`. -/
example (θ θ' : R2) : ‖gradient quadratic θ - gradient quadratic θ'‖ ≤ 1 * ‖θ - θ'‖ := by
  simp [quadratic_gradient]

/-! The step is defined on probability laws: under the zero measure, for which the step would be
the zero measure, it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : Measure R2 := lmcStep (fun _ : R2 => (0 : ℝ)) 1 0

end MathlibExtTest.LangevinMonteCarlo
