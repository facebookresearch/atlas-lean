/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.WeightedSum

namespace MetaMathlibExt

open Finset

-- At the lower endpoint, the identity determines the sign convention for B₁.
example : bernoulli 1 = -1 / 2 := by
  have h := sum_bernoulli_one_sub_two_pow 1 (by decide)
  norm_num only [Icc_self, sum_singleton, Nat.choose_self, Nat.cast_one, div_one, pow_one] at h
  linarith only [h]

-- The first sum with two terms recovers B₂ from B₁.
example : bernoulli 2 = 1 / 6 := by
  have h := sum_bernoulli_one_sub_two_pow 2 (by decide)
  rw [show Icc 1 2 = {1, 2} by decide, sum_pair (by decide : (1 : ℕ) ≠ 2)] at h
  norm_num only [Nat.choose_one_right, Nat.choose_self, Nat.cast_ofNat, Nat.cast_one,
    bernoulli_one] at h
  linarith only [h]

end MetaMathlibExt
