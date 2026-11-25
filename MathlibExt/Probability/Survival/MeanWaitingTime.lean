/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrated survival for a deterministic hazard rate

For a nonnegative locally integrable rate `h`, the survival function with hazard `c * h`
is `exp (-c * ∫ r in 0..t, h r)` for `c ≥ 0` and `t ≥ 0`. Its integral is the mean waiting
time when finite. The real-valued Bochner integral takes the value zero when not integrable.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The integral of the survival function for a scaled deterministic hazard. -/
noncomputable def meanWaitingTime (h : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-c * ∫ r in (0 : ℝ)..t, h r)

/-- A zero hazard gives the non-integrable constant survival function. -/
@[simp] theorem meanWaitingTime_zero_hazard (c : ℝ) : meanWaitingTime (fun _ => 0) c = 0 := by
  simp [meanWaitingTime, Measure.real, Real.volume_Ioi]

/-- Integrated survival is nonnegative, including when the integral is undefined. -/
theorem meanWaitingTime_nonneg (h : ℝ → ℝ) (c : ℝ) : 0 ≤ meanWaitingTime h c :=
  integral_nonneg fun _ => (Real.exp_pos _).le

end ProbabilityTheory
