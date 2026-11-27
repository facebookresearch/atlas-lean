/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JakobczykFermatNotPowPowModEqOneOfLt

/-! # Tests for `MathlibExt.NumberTheory.JakobczykFermatNotPowPowModEqOneOfLt` -/

namespace MathlibExtTest.NumberTheory.JakobczykFermatNotPowPowModEqOneOfLt

open MetaMathlibExt

-- `3 ^ 2 ^ 2 = 81 ≢ 1 [MOD 7]`, so the smaller power `3 ^ 2 ^ 1 = 9 ≢ 1 [MOD 7]`.
example : ¬ 3 ^ 2 ^ 1 ≡ 1 [MOD 7] :=
  not_pow_pow_modEq_one_of_lt (a := 3) (b := 2) (m := 7) (n := 2) (t := 1) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- Contrapositive: a smaller iterated power congruent to one forces the larger one to be one.
example {a b m n t : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hm : 2 ≤ m) (hn : 1 ≤ n)
    (h : a ^ b ^ t ≡ 1 [MOD m]) (ht : t < n) : a ^ b ^ n ≡ 1 [MOD m] := by
  by_contra hcon
  exact not_pow_pow_modEq_one_of_lt ha hb hm hn hcon ht h

end MathlibExtTest.NumberTheory.JakobczykFermatNotPowPowModEqOneOfLt
