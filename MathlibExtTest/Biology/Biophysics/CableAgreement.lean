/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CableAgreement

/-! Tests: unit cable parameters. -/

namespace MathlibExtTest.Biology.Biophysics.CableAgreement

open MathlibExt.Biology.Biophysics.CableAgreement

/-- At `rm = ri = cm = 1`, the constants are `1`. -/
example : (0:ℝ) < 1 * 1 ∧ Real.sqrt (1 / 1) ^ 2 * 1 = 1 ∧ 0 < Real.sqrt (1 / 1 : ℝ) :=
  cable_parameters one_pos one_pos one_pos

end MathlibExtTest.Biology.Biophysics.CableAgreement
