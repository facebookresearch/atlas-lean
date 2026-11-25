/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PowAddPowEqSqOppositeParity

/-! # Tests for opposite parity in `n^x + (5p)^y = z^2` -/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- When the first exponent is zero, the second can be odd: 1 + 15 = 16.
example : 0 % 2 ≠ 1 % 2 :=
  opposite_parity 3 3 0 1 4 (by decide) rfl rfl rfl

-- When the second exponent is zero, the first can be odd: 3 + 1 = 4.
example : 1 % 2 ≠ 0 % 2 :=
  opposite_parity 3 3 1 0 2 (by decide) rfl rfl rfl

-- Equal exponents are excluded for every square.
example (k z : ℕ) : 7 ^ k + 15 ^ k ≠ z ^ 2 :=
  fun h => opposite_parity 7 3 k k z (by decide) rfl rfl h rfl

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
