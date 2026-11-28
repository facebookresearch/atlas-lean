/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne

/-! # Tests for `MathlibExt.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne` -/

namespace MathlibExtTest.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne

open MetaMathlibExt

-- The least admissible base satisfies the congruence, so its repunits contain
-- infinitely many Riesel numbers.
example : {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧
    N = repstring 16518444216571 1 0 t ∧ IsRieselNumber N}.Infinite :=
  infinite_riesel_repunits_mod_two_pow_64_sub_one (b := 16518444216571) (by decide)

-- The next admissible base `16518444216571 + (2 ^ 64 - 1)` is even, so it exercises the
-- even-base parity branch; its repunits also contain infinitely many Riesel numbers.
example : {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧
    N = repstring 18446760592153768186 1 0 t ∧ IsRieselNumber N}.Infinite :=
  infinite_riesel_repunits_mod_two_pow_64_sub_one (b := 18446760592153768186) (by decide)

end MathlibExtTest.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne
