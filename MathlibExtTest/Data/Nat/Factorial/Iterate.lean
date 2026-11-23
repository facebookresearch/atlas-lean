/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.Factorial.Iterate

/-! # Tests for `MathlibExt.Data.Nat.Factorial.Iterate` -/

namespace MathlibExtTest.Data.Nat.Factorial.Iterate

open MetaMathlibExt

-- The smallest case `n = n' = 3`, `k = 1`, `k' = 0`: `3 < 3! = 6`.
example : Nat.factorial^[0] 3 < Nat.factorial^[1] 3 :=
  iterate_factorial_lt_iterate_factorial (Nat.le_refl 3) (Nat.le_refl 3) Nat.zero_lt_one
    (by decide)

-- Depths far beyond evaluation: `((4!)!)! < (((3!)!)!)!`, since `4 < 3! = 6`.
example : Nat.factorial^[3] 4 < Nat.factorial^[4] 3 :=
  iterate_factorial_lt_iterate_factorial (n := 3) (n' := 4) (k := 4) (k' := 3) (by decide)
    (by decide) (by decide) (by decide)

-- The hypothesis `n' < F_{k-k'}(n)` cannot be relaxed to `≤`: for `n' = 3! = 6`, `k = 2` and
-- `k' = 1`, both sides equal `6! = 720`.
example : Nat.factorial^[1] 6 = Nat.factorial^[2] 3 := by decide

-- The condition `k' < k` cannot be dropped: for `k = 0` and `k' = 1` the truncated difference
-- `k - k'` is `0`, so `n' = 3 < 4 = n` meets the other hypotheses, yet `3! = 6` exceeds `4`.
example : 3 < Nat.factorial^[0 - 1] 4 ∧ ¬Nat.factorial^[1] 3 < Nat.factorial^[0] 4 := by decide

end MathlibExtTest.Data.Nat.Factorial.Iterate
