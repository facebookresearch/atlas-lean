/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.Choose.AlternatingRowSums

namespace MetaMathlibExt

open Finset

-- The upper indices at i = 1 and i = 2 are negative, and both terms contribute.
example : ∑ i ∈ range 4, (-1 : ℤ) ^ i * Ring.choose ((i : ℤ) + 1 - 3 - 1) i = 4 :=
  (alternating_choose_mul_sum_choose 1 3).symm.trans (by decide)

-- For n < ℓ the weighted sum stops before the end of row ℓ.
example : ∑ i ∈ range 3, ((6 : ℕ).choose i : ℤ) * (-1) ^ i *
    ∑ j ∈ range (2 - i + 1), ((2 - i).choose j : ℤ) = 7 := by
  rw [alternating_choose_mul_sum_choose 6 2]
  decide

end MetaMathlibExt
