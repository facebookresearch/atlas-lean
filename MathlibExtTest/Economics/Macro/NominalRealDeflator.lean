/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macro.NominalRealDeflator
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macro.NominalRealDeflator` -/

namespace MathlibExtTest.Economics.Macro.NominalRealDeflator

open MathlibExt.Economics.Macro.NominalRealDeflator

example : (220 : ℝ) = 2 * realValue 220 2 :=
  nominal_eq_priceIndex_mul_real (by norm_num)

example : (2 : ℝ) = 220 / 110 :=
  priceIndex_eq_nominal_div_real (by norm_num) (by norm_num [realValue, nominalValue])

end MathlibExtTest.Economics.Macro.NominalRealDeflator
