/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Algebra.AffineRecurrenceConvergence

/-!
# Periodic dose steady state

For `0 ≤ q < 1`, post-dose amounts tend to the steady-state peak `D / (1 - q)` and
troughs to `q D / (1 - q)`.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseSteadyState

/-- **Steady-state post-dose limit.** For `0 ≤ q < 1`, the
post-dose amounts `x n = q^n * x0 + D * ∑ j ∈ range n, q^j` tend to
`D / (1 - q)`: the limiting peak (post-dose) amount. -/
lemma post_dose_tendsto {D q x0 : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j)
      atTop (𝓝 (D / (1 - q))) := by
  have hx : ∀ n : ℕ, (q ^ (n + 1) * x0 + D * ∑ j ∈ Finset.range (n + 1), q ^ j) =
      q * (q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j) + D := by
    intro n
    rw [pow_succ', geom_sum_succ]
    ring
  have habs : |q| < 1 := abs_lt.mpr ⟨by linarith, hq1⟩
  have h := MathlibExt.AffineRecurrence.affine_tendsto_fixedPoint
    (x := fun n : ℕ => q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j) hx habs
  exact h

/-- **Steady-state trough.** For `0 ≤ q < 1`, the pre-dose (trough) amounts `q * x n` tend to
`q * D / (1 - q)`. -/
lemma trough_tendsto {D q x0 : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => q * (q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j))
      atTop (𝓝 (q * D / (1 - q))) := by
  have h : Tendsto (fun n : ℕ => q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j)
      atTop (𝓝 (D / (1 - q))) :=
    post_dose_tendsto hq0 hq1
  have hMul : Tendsto (fun n : ℕ => q * (q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j))
      atTop (𝓝 (q * (D / (1 - q)))) :=
    h.const_mul q
  have hEq : q * (D / (1 - q)) = q * D / (1 - q) := by
    ring
  rwa [hEq] at hMul

end MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseSteadyState
