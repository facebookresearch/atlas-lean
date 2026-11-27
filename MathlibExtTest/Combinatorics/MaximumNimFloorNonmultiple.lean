/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MaximumNimFloorNonmultiple

/-! # Tests for `MathlibExt.Combinatorics.MaximumNimFloorNonmultiple` -/

namespace MathlibExtTest.MaximumNimFloorNonmultiple

open MetaMathlibExt

-- The first non-multiple has an empty option window. It reduces to the empty pile.
example (k : ℕ) (hk : 2 ≤ k) :
    maximumNimGrundy (· / k) 1 = maximumNimGrundy (· / k) 0 := by
  have hk1 : 1 < k := hk
  have hF : (k - 1) * 1 / k = 0 := by
    rw [Nat.mul_one, Nat.div_eq_of_lt (by omega : k - 1 < k)]
  simpa only [hF] using maximumNimGrundy_eq_F_of_not_dvd k 1 hk
    (Nat.not_dvd_of_pos_of_lt Nat.one_pos hk1)

-- At `k = 2` the non-multiple `5` reduces to `2` and has Grundy value `1`.
example : maximumNimGrundy (· / 2) 5 = 1 := by
  calc
    maximumNimGrundy (· / 2) 5 = maximumNimGrundy (· / 2) 2 :=
      maximumNimGrundy_eq_F_of_not_dvd 2 5 (by decide) (by decide)
    _ = 1 := maximumNimGrundy_div_eq_of_dvd 2 2 (by decide) (by decide) (by decide)

-- Just after the window grows at `9`, the pile `10` reduces to `6`, not to `9`.
example : maximumNimGrundy (· / 3) 10 = 2 := by
  calc
    maximumNimGrundy (· / 3) 10 = maximumNimGrundy (· / 3) 6 :=
      maximumNimGrundy_eq_F_of_not_dvd 3 10 (by decide) (by decide)
    _ = 2 := maximumNimGrundy_div_eq_of_dvd 3 6 (by decide) (by decide) (by decide)

-- The divisibility condition matters: at `6` the same floor map leads to `4`, and
-- `4` reduces to `2`, a terminal pile for the divisor `3`.
example : maximumNimGrundy (· / 3) 6 ≠ maximumNimGrundy (· / 3) ((3 - 1) * 6 / 3) := by
  change maximumNimGrundy (· / 3) 6 ≠ maximumNimGrundy (· / 3) 4
  rw [maximumNimGrundy_div_eq_of_dvd 3 6 (by decide) (by decide) (by decide),
    maximumNimGrundy_eq_F_of_not_dvd 3 4 (by decide) (by decide)]
  have h : maximumNimGrundy (· / 3) 2 = 0 :=
    maximumNimGrundy_sub_eq_zero 3 1 (by decide) (by decide) (by decide)
  change 2 ≠ maximumNimGrundy (· / 3) 2
  rw [h]
  decide

end MathlibExtTest.MaximumNimFloorNonmultiple
