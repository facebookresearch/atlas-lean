/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Periodic dosing trajectory

A fixed-spacing periodic dosing schedule (`tau > 0`, dose `D`,
decay rate `k`) defines an amount trajectory by finite dose sums;
between events it is the post-dose amount decayed freely. No
differentiability at dose jumps is claimed.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing

/-- The amount just after dose `n` in the fixed-spacing trajectory:
the sum of the first `n + 1` doses, each decayed from its event
time to `n * tau`. This is the event-time value of the trajectory
in `periodic_amount_decay`. -/
noncomputable def postDoseAmount (D k tau : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    D * Real.exp (-k * ((n : ℝ) * tau - (i : ℝ) * tau))

set_option linter.unusedVariables false in
/-- **Decay between events.** For `t` in the window
`[n * tau, (n + 1) * tau)` of the fixed-spacing schedule (so
`⌊t / tau⌋₊ = n`), the amount
`A t = ∑ i ∈ range (⌊t / tau⌋₊ + 1), D * exp (-k * (t - i * tau))`
is the amount just after the `n`-th dose decayed freely over
`t - n * tau`. The dose at `t = n * tau` itself is included (the
`i = n` term is `D * exp 0 = D` at the event instant). -/
lemma periodic_amount_decay {D k tau t : ℝ} (htau : 0 < tau) (ht : 0 ≤ t) (n : ℕ)
    (hfloor : ⌊t / tau⌋₊ = n) :
    (∑ i ∈ Finset.range (⌊t / tau⌋₊ + 1),
      D * Real.exp (-k * (t - i * tau))) =
      Real.exp (-k * (t - n * tau)) * postDoseAmount D k tau n := by
  rw [hfloor, postDoseAmount, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : -k * (t - (i : ℝ) * tau) =
      -k * (t - (n : ℝ) * tau) + -k * ((n : ℝ) * tau - (i : ℝ) * tau) := by
    ring
  rw [h, Real.exp_add]
  ring

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing
