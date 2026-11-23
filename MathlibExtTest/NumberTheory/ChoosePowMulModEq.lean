/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ChoosePowMulModEq

/-!
# Tests for binomial coefficients scaled by a prime power
-/

namespace MetaMathlibExt

-- Scaling both arguments by 3² preserves the nonzero residue of 2 choose 1.
example : (18 : ℕ).choose 9 ≡ 2 [MOD 3] :=
  choose_pow_mul_modEq (a := 2) (b := 1) (r := 2) (by decide) (by decide)
    (by decide) (by decide)

-- At the least allowed exponent, the lower argument may still exceed the upper one.
example {p a b : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) (hab : a < b) :
    (p * a).choose (p * b) ≡ 0 [MOD p] := by
  simpa only [pow_one, Nat.choose_eq_zero_of_lt hab] using
    choose_pow_mul_modEq (r := 1) hp le_rfl hpa hpb

end MetaMathlibExt
