/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSum

namespace MetaMathlibExt

-- The first odd order with a nontrivial factorial detects the sign and the scale.
example (a : ℂ) :
    ∑ i ∈ Finset.range 4, (-1 : ℂ) ^ i * (Nat.choose 3 i : ℂ) * (a + i * 2) ^ 3 = -48 := by
  have h := (sum_neg_one_pow_choose_mul_pow a 2 1 (n := 3) (m := 3) (by decide) (by decide)).1 rfl
  norm_num [Nat.factorial] at h
  exact h

-- One difference past the degree annihilates an affine power.
example (a y : ℂ) {m : ℕ} (hm : 0 < m) :
    ∑ i ∈ Finset.range (m + 2),
      (-1 : ℂ) ^ i * ((m + 1).choose i : ℂ) * (a + i * y) ^ m = 0 := by
  simpa using (sum_neg_one_pow_choose_mul_pow a y 1 (Nat.succ_pos m) hm).2 (Nat.lt_succ_self m)

-- With zero increment the sum vanishes even when the order equals the exponent.
example (a : ℂ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * (n.choose i : ℂ) * a ^ n = 0 := by
  simpa [zero_pow hn.ne'] using (sum_neg_one_pow_choose_mul_pow a 0 1 hn hn).1 rfl

end MetaMathlibExt
