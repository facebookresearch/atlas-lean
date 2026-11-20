/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseRecurrence

/-! Tests: two steps of the recurrence. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseRecurrence

open MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseRecurrence

/-- Event-time bridge at dose `2`, spacing `1`. -/
example :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        3 0 1 2 =
      ∑ i ∈ Finset.range (⌊(2 : ℝ) * 1 / 1⌋₊ + 1),
        (3:ℝ) * Real.exp (-(0:ℝ) * ((2:ℝ) * 1 - (i:ℝ) * 1)) :=
  postDoseAmount_at_event (by norm_num) 2

/-- Successor recurrence at dose `2`, symbolic elimination. -/
example (D k tau : ℝ) :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        D k tau (2 + 1) =
      Real.exp (-k * tau) *
          MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
            D k tau 2 + D :=
  post_dose_amount_succ 2

/-- Closed form at dose `2`, symbolic elimination. -/
example (D k tau : ℝ) :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        D k tau 2 =
      Real.exp (-k * tau) ^ 2 * D +
        D * ∑ j ∈ Finset.range 2, Real.exp (-k * tau) ^ j :=
  post_dose_amount_closed_form 2

/-- No elimination at `D = 3`, after dose `2`: three doses give `9`. -/
example :
    MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing.postDoseAmount
        3 0 1 2 = 9 := by
  rw [post_dose_amount_zero_elimination]
  norm_num

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseRecurrence
