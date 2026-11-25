/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IntegerComplexityRecurrence

open MathlibExt.NumberTheory.IntegerComplexityWanted

-- At two, multiplying by one costs an extra one, so the minimum comes from 1 + 1.
example : cx 2 = 2 := by
  have hone : cx 1 = 1 := IntegerComplexity.complexity_one
  rcases (complexity_eq_min 2 (by decide)).1 with ⟨d, hd, hdvd, h⟩ | ⟨j, hj, hjn, h⟩
  · have := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    obtain rfl : d = 2 := by omega
    change cx 2 = cx 2 + cx 1 at h
    omega
  · obtain rfl : j = 1 := by omega
    change cx 2 = cx 1 + cx 1 at h
    omega

-- The factor 6 is above the square root of 12 and is still an admissible divisor.
example : cx 12 ≤ cx 6 + cx 2 :=
  (complexity_eq_min 12 (by decide)).2 (Or.inl ⟨6, by decide, by decide, rfl⟩)

-- For an odd input, the largest allowed smaller summand is the floor of half the input.
example : cx 5 ≤ cx 2 + cx 3 :=
  (complexity_eq_min 5 (by decide)).2 (Or.inr ⟨2, by decide, by decide, rfl⟩)
