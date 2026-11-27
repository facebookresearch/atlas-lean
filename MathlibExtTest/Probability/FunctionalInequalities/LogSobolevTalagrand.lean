/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FunctionalInequalities.LogSobolevTalagrand
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Filter Topology MathlibExt.Probability.LogSobolevTalagrand

namespace MathlibExtTest.Probability.FunctionalInequalities.LogSobolevTalagrand

/-- Non-vacuity: the Dirac mass at `0` on `ℝ` satisfies the logarithmic Sobolev inequality with
constant `1`. -/
example : SatisfiesLogSobolev (Measure.dirac (0 : ℝ)) 1 := satisfiesLogSobolev_dirac 0 1

/-! The log-Sobolev inequality is stated for probability measures: for the zero measure, which
would satisfy it vacuously (no density integrates to `1`), it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Prop := SatisfiesLogSobolev (0 : Measure ℝ) 1

/-- Non-vacuity: the Dirac mass at `0` on `ℝ` satisfies Talagrand's inequality with constant `2`,
the constant that the Otto–Villani theorem produces from the log-Sobolev constant `1`. -/
example : SatisfiesTalagrand (⟨Measure.dirac (0 : ℝ), inferInstance⟩ : ProbabilityMeasure ℝ)
    (2 / 1) :=
  satisfiesTalagrand_dirac 0 (by norm_num)

/-- The `W₁` bound for the Dirac mass at `0` on `ℝ`. -/
example (μ : ProbabilityMeasure ℝ) :
    MathlibExt.MeasureTheory.OptimalTransport.Wasserstein.wasserstein 1 μ
        (⟨Measure.dirac (0 : ℝ), inferInstance⟩ : ProbabilityMeasure ℝ) ^ (2 : ℝ) ≤
      ENNReal.ofReal 2 * InformationTheory.klDiv (μ : Measure ℝ) (Measure.dirac 0) :=
  (satisfiesTalagrand_dirac 0 (by norm_num : (0 : ℝ) < 2)).wasserstein_one_sq_le μ

/-- The local Lipschitz constant of a constant function vanishes. -/
example (c x : ℝ) : localLipschitzConstant (fun _ : ℝ => c) x = 0 := by
  simp [localLipschitzConstant]

/-- The local Lipschitz constant of the identity of `ℝ` is `1` at every point: the difference
quotient is identically `1` on the punctured neighbourhood. -/
example (x : ℝ) : localLipschitzConstant (fun y : ℝ => y) x = 1 := by
  have h : ∀ᶠ y in 𝓝[≠] x, ENNReal.ofReal (|y - x| / dist y x) = 1 := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have hne : |y - x| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hy)
    rw [Real.dist_eq, div_self hne, ENNReal.ofReal_one]
  rw [localLipschitzConstant, Filter.limsup_congr h, Filter.limsup_const]

end MathlibExtTest.Probability.FunctionalInequalities.LogSobolevTalagrand
