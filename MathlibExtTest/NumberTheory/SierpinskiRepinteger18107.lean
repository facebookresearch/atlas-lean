/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SierpinskiRepinteger18107

namespace MetaMathlibExt

-- The first admissible length gives the geometric quotient for 25 blocks of 15 bits.
example : IsSierpinskiNumber (18107 * (2 ^ 375 - 1) / 32767) := by
  rw [← show repstring 2 18107 0 25 = 18107 * (2 ^ 375 - 1) / 32767 by decide +kernel]
  exact isSierpinskiNumber_repstring_18107 (t := 25) (ht := by decide)

-- After one length period, specialize to the smallest allowed exponent.
example : ¬ (repstring 2 18107 0 81 * 2 + 1).Prime := by
  have hk := isSierpinskiNumber_repstring_18107 (t := 81) (by decide)
  simpa only [pow_one] using hk.2 1 le_rfl

end MetaMathlibExt
