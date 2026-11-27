/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul

/-! # Tests for `MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul` -/

namespace MathlibExtTest.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul

open MathlibExt.NumberTheory.FkPerfectWanted

-- `24 = 2 ^ 3 * 3` is not `[2,1]`-near-perfect.
example : ¬ IsKLNearPerfect 2 1 (2 ^ 3 * 3) :=
  not_isKLNearPerfect_two_two_pow_mul 1 3 3 le_rfl (by decide) (by decide)

-- `20 = 2 ^ 2 * 5` is not `[2,ℓ]`-near-perfect for any `ℓ ≥ 1`.
example (l : ℕ) (hl : 1 ≤ l) : ¬ IsKLNearPerfect 2 l (2 ^ 2 * 5) :=
  not_isKLNearPerfect_two_two_pow_mul l 5 2 hl (by decide) (by decide)

-- At `a = 0` the number `7 = 2 ^ 0 * 7` is prime, hence not `[2,7]`-near-perfect.
example : ¬ IsKLNearPerfect 2 7 (2 ^ 0 * 7) :=
  not_isKLNearPerfect_two_two_pow_mul 7 7 0 (by decide) (by decide) (by decide)

end MathlibExtTest.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul
