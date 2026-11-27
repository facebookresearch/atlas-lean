/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.PharmacokineticObservation.FixedLaw

/-! Tests for the PK log law on a three-visit design. -/

namespace MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.FixedLaw

open MathlibExt.Biology.Biophysics.PharmacokineticObservation

/-- Three visits `t = ![0, 1, 2]`, errors `![0, 1/10, -1/10]`,
`D = 100`, `V = 10`, `k = 2`: each log observation is the exact
linear form. -/
example (j : Fin 3) :
    Real.log ((100 / 10 : ℝ) * Real.exp (-2 * ![0, 1, 2] j) * Real.exp (![0, 1/10, -1/10] j)) =
      1 * Real.log (100 / 10) + (-![0, 1, 2] j) * 2 + ![0, 1/10, -1/10] j :=
  pk_log_law (by norm_num) (by norm_num) ![0, 1, 2] ![0, 1/10, -1/10] j

end MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.FixedLaw
