/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LambertSequencePartialExpSum

namespace MetaMathlibExt

-- The largest admissible truncation at the first Lambert index in the theorem.
example (a : ℝ) (ha : 4 ≤ a)
    (hW : lambertMap (-a / 4) = -(1 / 4) * (4 / 7 : ℝ) ^ (1 / 4 : ℝ)) :
    1 + a + a ^ 2 / 2 < a ^ 3 / 6 := by
  have h := sum_pow_div_factorial_lt_lambertSequence 5 2 (by decide) (by decide) a
    (by norm_num; exact ha) (by norm_num at hW ⊢; exact hW)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact h

end MetaMathlibExt
