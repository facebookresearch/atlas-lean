/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.TaxShield
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.TaxShield

open MathlibExt.Economics.Finance.TaxShield

example : taxShieldValue (3/10) (1/20) 1000 = 300 := by
  rw [perpetual_taxShield_value (by norm_num)]
  norm_num

example {rD D : ℝ} (hrD : 0 < rD) : taxShieldValue 0 rD D = 0 := by
  rw [perpetual_taxShield_value hrD, zero_mul]

end MathlibExtTest.Economics.Finance.TaxShield
