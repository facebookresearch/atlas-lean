/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.ClassificationCalibration
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.NormNum

/-!
# Classification-calibration tests

The exponential loss `exp (-α)` of AdaBoost and the hinge loss `max 0 (1 - α)` of support
vector machines are convex, nonnegative and have slope `-1` at `0`, so both are
classification-calibrated (Bartlett, Jordan and McAuliffe, Examples 1 and 4). The conditional
risk is reflected by `η ↦ 1 - η`.
-/

namespace Cslib.MachineLearning.ClassificationCalibration

open Real

example (η α : ℝ) : condRisk (fun x => exp (-x)) η α =
    η * exp (-α) + (1 - η) * exp α := by
  simp [condRisk]

/-- The exponential loss is classification-calibrated. -/
example : IsClassificationCalibrated fun x => exp (-x) := by
  refine isClassificationCalibrated_of_hasDerivAt (d := -1) (fun x => (exp_pos _).le) ?_ ?_
    (by norm_num)
  · simpa [Function.comp_def] using
      convexOn_exp.comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  · have := (hasDerivAt_neg (0 : ℝ)).exp
    simpa using this

/-- The hinge loss is classification-calibrated. -/
example : IsClassificationCalibrated fun x => max 0 (1 - x) := by
  refine isClassificationCalibrated_of_hasDerivAt (d := -1) (fun x => le_max_left _ _) ?_ ?_
    (by norm_num)
  · have hlin : ConvexOn ℝ Set.univ fun x : ℝ => 1 - x := by
      have := ((-LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn convex_univ).add_const 1
      exact this.congr fun x _ => by simp; ring
    exact (convexOn_const 0 convex_univ).sup hlin
  · have h : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact max_eq_right (by simp at hx; linarith)

end Cslib.MachineLearning.ClassificationCalibration
