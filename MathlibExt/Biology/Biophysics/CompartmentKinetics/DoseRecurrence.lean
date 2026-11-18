/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Algebra.AffineRecurrence
public import MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing

/-!
# Periodic dose recurrence

Post-dose amounts in the fixed-spacing trajectory obey the affine recurrence with ratio
`exp (-k * tau)`, with the corresponding closed form.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseRecurrence

/-- **Event-time bridge.** At the event time `t = n * tau`
(`tau > 0`), the trajectory sum of `periodic_amount_decay` is
exactly `postDoseAmount D k tau n`. -/
lemma postDoseAmount_at_event {D k tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        D k tau n =
      ∑ i ∈ Finset.range (⌊(n : ℝ) * tau / tau⌋₊ + 1),
        D * Real.exp (-k * ((n : ℝ) * tau - (i : ℝ) * tau)) := by
  have hfloor : ⌊(n : ℝ) * tau / tau⌋₊ = n := by
    rw [mul_div_cancel_right₀ _ htau.ne', Nat.floor_natCast]
  rw [hfloor]
  rfl

/-- **Post-dose amounts satisfy the affine recurrence.** The
amount just after dose `n + 1` is the amount just after dose `n`,
decayed by `exp (-k * tau)`, plus the new dose `D`. -/
lemma post_dose_amount_succ {D k tau : ℝ} (n : ℕ) :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        D k tau (n + 1) =
      Real.exp (-k * tau) *
          MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
            D k tau n + D := by
  unfold MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
  rw [Finset.sum_range_succ]
  have hlast : D * Real.exp (-k * (((n + 1 : ℕ) : ℝ) * tau -
      ((n + 1 : ℕ) : ℝ) * tau)) = D := by
    simp
  rw [hlast]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hexp : -k * (((n + 1 : ℕ) : ℝ) * tau - (i : ℝ) * tau) =
      -k * tau + -k * ((n : ℝ) * tau - (i : ℝ) * tau) := by
    push_cast
    ring
  rw [hexp, Real.exp_add]
  ring

/-- **No-elimination boundary.** At `k = 0` the amount just after
dose `n` is `(n + 1) * D`: `n + 1` undecayed doses. -/
lemma post_dose_amount_zero_elimination {D tau : ℝ} (n : ℕ) :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        D 0 tau n =
      ((n : ℝ) + 1) * D := by
  unfold MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Post-dose closed form for the periodic trajectory.** The
amount just after dose `n` is
`exp (-k * tau)^n * D + D * ∑ j ∈ range n, exp (-k * tau)^j`,
derived from `post_dose_amount_succ` through the affine-recurrence
closed form. -/
lemma post_dose_amount_closed_form {D k tau : ℝ} (n : ℕ) :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        D k tau n =
      Real.exp (-k * tau) ^ n * D +
        D * ∑ j ∈ Finset.range n, Real.exp (-k * tau) ^ j := by
  have h := MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_pow_mul_add_geom_sum
    (x := MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
      D k tau)
    (a := Real.exp (-k * tau)) (b := D)
    (fun m => post_dose_amount_succ m) n
  have h0 :
      MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
          D k tau 0 = D := by
    unfold MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
    simp
  rwa [h0] at h

end MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseRecurrence
