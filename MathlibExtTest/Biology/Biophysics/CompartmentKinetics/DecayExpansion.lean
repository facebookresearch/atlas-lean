/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion

/-! Tests: distinct and equal rates. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DecayExpansion

open MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion

/-- Distinct rates `ke = 1 < ka = 2`, `A = 3`, `t = 1`. -/
example : 0 ≤ 3 * (Real.exp (-1 * 1) - Real.exp (-2 * 1)) / (2 - 1) :=
  decay_expansion_nonneg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Equal-rate form. -/
example : 0 ≤ 3 * 1 * Real.exp (-2 * 1) :=
  decay_equal_rate_nonneg (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DecayExpansion
