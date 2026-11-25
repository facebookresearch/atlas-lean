/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Survival.MeanWaitingTime
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Tests for integrated survival under a scaled hazard -/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- A unit baseline with multiplier `c > 0` has the exponential waiting time mean `1 / c`. -/
example {c : ℝ} (hc : 0 < c) : meanWaitingTime (fun _ => 1) c = c⁻¹ := by
  simpa [meanWaitingTime] using integral_exp_mul_Ioi (neg_neg_of_pos hc) 0

/-- A zero multiplier gives the non-integrable constant tail, whose Bochner integral is zero. -/
example (h : ℝ → ℝ) : meanWaitingTime h 0 = 0 := by
  simp [meanWaitingTime, Measure.real, Real.volume_Ioi]
