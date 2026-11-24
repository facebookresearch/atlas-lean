/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- The empirical risk is the sample average of the losses.
example : empiricalRisk (fun (_ : Unit) (z : ℝ) => z) ![1, 3] () = 2 := by
  simp [empiricalRisk, Fin.sum_univ_two]
  norm_num

-- Empirical risk minimization on two predictors with deviations at most `1/10`.
example : (fun b : Bool => if b then (0.3 : ℝ) else 0.5) true ≤
    (fun b : Bool => if b then (0.3 : ℝ) else 0.5) false + 2 * (1 / 10) := by
  have := risk_le_add_two_mul_of_forall_abs_sub_le
    (R := fun b : Bool => if b then (0.3 : ℝ) else 0.5)
    (Rhat := fun b : Bool => if b then (0.25 : ℝ) else 0.55) (fhat := true)
    (fun f => by cases f <;> norm_num) (s := 1 / 10)
    (fun f => by cases f <;> norm_num [abs_le]) false
  exact this

/-! The risk is taken under a probability measure and the empirical risk over a nonempty
sample: under the zero measure, or on an empty sample, every predictor would get risk `0`. -/

/--
error: failed to synthesize instance of type class
  MeasureTheory.IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : ℝ := risk (fun (_ : Unit) (z : ℝ) => z) (0 : MeasureTheory.Measure ℝ) ()

/--
error: failed to synthesize instance of type class
  NeZero 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : ℝ := empiricalRisk (fun (_ : Unit) (z : ℝ) => z) (![] : Fin 0 → ℝ) ()

end CSLibExt.MachineLearning.GeneralizationBounds
