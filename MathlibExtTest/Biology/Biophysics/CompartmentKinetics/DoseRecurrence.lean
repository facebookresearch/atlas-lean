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

/-- Closed form at `k = 0`, `D = 3`, after dose `2`: three doses of `3`. -/
example :
    (∑ i ∈ Finset.range (2 + 1),
        (3:ℝ) * Real.exp (-(0:ℝ) * ((2:ℝ) * 1 - (i:ℝ) * 1))) =
      Real.exp (-(0:ℝ) * 1) ^ 2 * 3 +
        3 * ∑ j ∈ Finset.range 2, Real.exp (-(0:ℝ) * 1) ^ j :=
  post_dose_amount_closed_form 2

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseRecurrence
