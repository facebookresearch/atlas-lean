/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Amicable

namespace MathlibExt.NumberTheory.AmicableWanted

-- At the lower endpoint the only abundancy index is σ(1)/1 = 1.
example : 1 < ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2 := by
  simpa using sum_sigma_div_lt 1 le_rfl

-- On [2, 3) the left side is σ(1)/1 + σ(2)/2 = 5/2.
example (x : ℝ) (hx : 2 ≤ x) (hx' : x < 3) :
    5 / 2 < (∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2) * x := by
  have hfloor : ⌊x⌋₊ = 2 := (Nat.floor_eq_iff (by linarith)).2 (by norm_num; exact ⟨hx, hx'⟩)
  have h := sum_sigma_div_lt x (by linarith)
  rw [hfloor, Finset.sum_Icc_succ_top (by decide : 1 ≤ 1 + 1)] at h
  have htwo : ArithmeticFunction.sigma 1 2 = 3 := by decide
  norm_num [htwo] at h ⊢
  linarith

-- With both coefficients zero, a positive first entry would have divisor sum zero.
example (x : ℕ) : multiamicablePairCount 0 0 x = 0 := by
  rw [multiamicablePairCount, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨p, hp⟩ ↦ ?_⟩
  have : p.1 = 0 := by simpa using hp.2.2.2.2
  exact hp.1.ne' this

end MathlibExt.NumberTheory.AmicableWanted
