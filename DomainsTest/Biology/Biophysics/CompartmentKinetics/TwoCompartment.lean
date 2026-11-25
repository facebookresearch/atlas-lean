/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.CompartmentKinetics.TwoCompartment

/-! Tests: numeric peripheral nonnegativity and the zero-dose case. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartment

open MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment

/-- Numeric instance, exercised through the API. -/
example : 0 ≤ ∫ s in (0:ℝ)..2,
    Real.exp (-1 * (2 - s)) * (1 * (10 * Real.exp (-(1 + 1) * s))) :=
  peripheral_amount_nonneg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Zero dose: the integrand is zero, so the amount is zero. -/
example : (∫ s in (0:ℝ)..2,
    Real.exp (-1 * (2 - s)) * (1 * (0 * Real.exp (-(1 + 1) * s)))) = 0 := by
  simp

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartment
