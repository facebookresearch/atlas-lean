/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-! Tests: depot initial value and central nonnegativity. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Absorption.Model

open MathlibExt.Biology.Biophysics.CompartmentKinetics.Absorption.Model

/-- Central amount is nonnegative at unit time. -/
example : 0 ≤ centralAmount 1 2 3 1 1 :=
  central_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Equal-rate central amount is nonnegative at unit time. -/
example : 0 ≤ centralAmountEqual 1 2 3 1 :=
  centralEqual_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The distinct-rate derivative witness at concrete rates. -/
example : HasDerivAt (centralAmount 1 2 3 1)
    (1 * 3 * depotAmount 2 3 1 - 1 * centralAmount 1 2 3 1 1) 1 :=
  central_hasDerivAt_distinct (by norm_num)

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Absorption.Model
