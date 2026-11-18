/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

/-! Tests: full-bioavailability budget derivative. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

open MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Budget

/-- At `F = 1` only central elimination remains. -/
example : deriv (fun t => depotAmount 2 3 t + centralAmount 1 2 3 1 t) 1 =
    -1 * centralAmount 1 2 3 1 1 :=
  budget_deriv_full (by norm_num)

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Absorption.Budget
