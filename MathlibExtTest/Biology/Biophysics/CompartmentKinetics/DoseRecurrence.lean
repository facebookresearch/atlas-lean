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

/-- `x 2` from the recurrence relation, via the closed form. -/
example (x : ℕ → ℝ) (h0 : x 0 = 5)
    (hstep : ∀ n, x (n + 1) = (1/2) * x n + 3) :
    x 2 = (1/2)^2 * 5 + 3 * ∑ j ∈ Finset.range 2, (1/2:ℝ)^j :=
  post_dose_closed_form x h0 hstep 2

/-- No elimination: `x 3 = x0 + 3D`. -/
example (x : ℕ → ℝ) (h0 : x 0 = 5)
    (hstep : ∀ n, x (n + 1) = 1 * x n + 3) : x 3 = 5 + 3 * 3 :=
  post_dose_no_elimination x h0 hstep 3

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseRecurrence
