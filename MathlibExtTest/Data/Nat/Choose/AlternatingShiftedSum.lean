/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.Choose.AlternatingShiftedSum

namespace MetaMathlibExt

open Finset

-- At ℓ = n, j = 1 and s = 0, the result is the corner entry of Pascal's triangle.
example {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), (n.choose i : ℤ) * (-1) ^ i * ((n - i).choose n : ℤ) = 1 := by
  simpa using alternating_sum_choose_mul_choose_sub (ℓ := n) (n := n) (j := 1) (s := 0)
    hn le_rfl le_rfl (by simp)

-- All four summands contribute, with a nonzero shift and j greater than one.
example :
    ∑ i ∈ range 4, ((3 : ℕ).choose i : ℤ) * (-1) ^ i * ((11 - i).choose 7 : ℤ) = 70 :=
  alternating_sum_choose_mul_choose_sub (ℓ := 3) (n := 11) (j := 2) (s := 1)
    (by decide) (by decide) (by decide) (by decide)

end MetaMathlibExt
