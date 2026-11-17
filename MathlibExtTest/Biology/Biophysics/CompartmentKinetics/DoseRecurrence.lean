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

/-- No elimination at `D = 3`, after dose `2`: three doses give `9`. -/
example :
    (∑ i ∈ Finset.range (2 + 1),
        (3:ℝ) * Real.exp (-(0:ℝ) * ((2:ℝ) * 1 - (i:ℝ) * 1))) = 9 := by
  have h := post_dose_amount_zero_elimination (D := (3:ℝ)) (tau := (1:ℝ)) 2
  simpa using h

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseRecurrence
