/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

/-! Tests: full-bioavailability budget derivative. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

open MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget
open MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-- At `F = 1` only central elimination remains. -/
example : deriv (fun t => depotAmount 2 3 t + centralAmount 1 2 3 1 t) 1 =
    -1 * centralAmount 1 2 3 1 1 :=
  budget_deriv_full (by norm_num)

/-- Equal-rate budget derivative at concrete rates. -/
example : deriv (fun t => depotAmount 2 3 t + centralAmountEqual 1 2 3 t) 1 =
    -(1 - 1) * 3 * depotAmount 2 3 1 - 3 * centralAmountEqual 1 2 3 1 :=
  budget_deriv_equal

/-- Equal-rate integrated budget at concrete rates. -/
example : (∫ s in (0:ℝ)..(1:ℝ), (-(1 - 1) * 3 * depotAmount 2 3 s -
      3 * centralAmountEqual 1 2 3 s)) =
      (depotAmount 2 3 1 + centralAmountEqual 1 2 3 1) -
        (depotAmount 2 3 0 + centralAmountEqual 1 2 3 0) :=
  budget_integral_equal

/-- Distinct-rate budget derivative with a genuine absorption loss at `F = 1/2`. -/
example : deriv (fun t => depotAmount 2 3 t + centralAmount (1/2) 2 3 1 t) 1 =
    -(1 - 1/2) * 3 * depotAmount 2 3 1 - 1 * centralAmount (1/2) 2 3 1 1 :=
  budget_deriv (F := 1/2) (D := 2) (ka := 3) (k := 1) (t := 1) (by norm_num)

/-- Canonical integrated budget at `F = 1/2`. -/
example : (∫ s in (0:ℝ)..(1:ℝ), (-(1 - 1/2) * 3 * depotAmount 2 3 s -
      1 * centralAmountCanonical (1/2) 2 3 1 s)) =
      (depotAmount 2 3 1 + centralAmountCanonical (1/2) 2 3 1 1) -
        (depotAmount 2 3 0 + centralAmountCanonical (1/2) 2 3 1 0) :=
  budget_integral_canonical

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Absorption.Budget
