/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite-horizon dose budget

Change in amount over a finite horizon is the included dose sum minus the integrated elimination, for events at positive times.
-/

@[expose] public section

open Finset intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseBudget

/-- **Finite-horizon dose budget.** If the amount `A` satisfies,
for every `t`, the integral equation with finitely many dose
events at times `eventTime i`, all positive (`hevent`) of sizes `dose i` and
continuous elimination rate `k`, then on `[0, T]` the change in
amount is the included dose sum minus `k` times the integrated
amount. The initial dose is not counted: events are in `(0, T]`. -/
theorem dose_budget_from_integral_equation {A : ℝ → ℝ} {A0 k T : ℝ}
    {m : ℕ} (eventTime dose : ℕ → ℝ)
    (hevent : ∀ i ∈ Finset.range m, 0 < eventTime i)
    (hA : ∀ t : ℝ, A t = A0 +
      (∑ i ∈ Finset.range m, if eventTime i ≤ t then dose i else 0) -
      k * ∫ s in (0:ℝ)..t, A s) :
    A T - A 0 =
      (∑ i ∈ Finset.range m, if eventTime i ≤ T then dose i else 0) -
      k * ∫ s in (0:ℝ)..T, A s := by
  have hT := hA T
  have h0 := hA (0 : ℝ)
  have hsum0 : (∑ i ∈ Finset.range m, if eventTime i ≤ (0 : ℝ) then dose i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (not_le_of_gt (hevent i hi))
  rw [hsum0, integral_same, mul_zero, add_zero, sub_zero] at h0
  linarith


end MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseBudget
