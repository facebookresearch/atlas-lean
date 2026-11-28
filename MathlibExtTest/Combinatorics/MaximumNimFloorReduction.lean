/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MaximumNimFloorReduction

/-! # Tests for `MathlibExt.Combinatorics.MaximumNimFloorReduction` -/

namespace MathlibExtTest.MaximumNimFloorReduction

open MetaMathlibExt

-- At the smallest divisor the reduction reaches the empty pile.
example : maximumNimGrundy (· / 2) 1 = maximumNimGrundy (· / 2) 0 :=
  (maximumNimGrundy_mul_sub_eq_F_eq_pred 2 1 1 1 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1

-- At `i = n` with `t > 1`, both equalities identify the reduced pile of size 15.
example : maximumNimGrundy (· / 7) 18 = maximumNimGrundy (· / 7) 15 := by
  obtain ⟨h₁, h₂⟩ := maximumNimGrundy_mul_sub_eq_F_eq_pred 7 3 2 1 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h₁.trans h₂

-- The reduced pile can be a multiple of the divisor even when the original pile is not.
example : maximumNimGrundy (· / 5) 13 = 2 := by
  obtain ⟨h₁, h₂⟩ := maximumNimGrundy_mul_sub_eq_F_eq_pred 5 3 1 2 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h₁.trans (h₂.trans (maximumNimGrundy_div_eq_of_dvd 5 10
    (by decide) (by decide) (by decide)))

end MathlibExtTest.MaximumNimFloorReduction
