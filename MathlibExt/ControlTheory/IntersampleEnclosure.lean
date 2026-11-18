/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Intersample displacement enclosure

Between samples, an actual trajectory can drift away from a
sampled approximation by at most the accumulated motion
bound: if `‖γ t - γ ts‖ ≤ vbar * (t - ts)` on `[ts, ts + h]`
and the approximation starts within `ε` of `γ ts`, then
`‖γ t - xhat‖ ≤ ε + vbar * h` on the whole interval.
-/

@[expose] public section

namespace ControlTheory

/-- Intersample displacement enclosure. If an actual curve
`γ` satisfies the displacement bound
`‖γ t - γ ts‖ ≤ vbar * (t - ts)` on the sample interval
`[ts, ts + h]`, and a sampled approximation `xhat` starts
within `ε` of `γ ts`, then `‖γ t - xhat‖ ≤ ε + vbar * h`
throughout the interval. The motion bound is an explicit
premise about the actual trajectory, not a consequence of
sample agreement. -/
theorem intersample_displacement_le
    {E : Type*} [NormedAddCommGroup E]
    {γ : ℝ → E} {xhat : E} {ts h vbar ε : ℝ} (hv : 0 ≤ vbar)
    (hmotion : ∀ t ∈ Set.Icc ts (ts + h), ‖γ t - γ ts‖ ≤ vbar * (t - ts))
    (hstart : ‖γ ts - xhat‖ ≤ ε) :
    ∀ t ∈ Set.Icc ts (ts + h), ‖γ t - xhat‖ ≤ ε + vbar * h := by
  intro t ht
  have hhi : t ≤ ts + h := (Set.mem_Icc.mp ht).2
  have hsub : t - ts ≤ h := by linarith
  have hmono : vbar * (t - ts) ≤ vbar * h :=
    mul_le_mul_of_nonneg_left hsub hv
  have heq : γ t - xhat = (γ t - γ ts) + (γ ts - xhat) := by abel
  calc ‖γ t - xhat‖ = ‖(γ t - γ ts) + (γ ts - xhat)‖ := by rw [heq]
    _ ≤ ‖γ t - γ ts‖ + ‖γ ts - xhat‖ := norm_add_le _ _
    _ ≤ vbar * (t - ts) + ε := add_le_add (hmotion t ht) hstart
    _ ≤ vbar * h + ε := add_le_add hmono le_rfl
    _ = ε + vbar * h := add_comm _ _

end ControlTheory
