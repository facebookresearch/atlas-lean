/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.OneStepPayoffMax

@[expose] public section

open MathlibExt.Analysis.SpecialFunctions.OneStepPayoffMax

namespace MathlibExtTest.Analysis.SpecialFunctions.OneStepPayoffMax

/-! ## The exact public statements -/

example {mMinus mPlus b a s : ℝ} (hb : 0 < b) (ha : 0 ≤ a)
    (hs : s = max 0 (Real.sqrt (b * (mPlus - mMinus)) - b)) :
    -a + (a * mPlus + b * mMinus) / (a + b) ≤ -s + (s * mPlus + b * mMinus) / (s + b) ∧
      (-a + (a * mPlus + b * mMinus) / (a + b) = -s + (s * mPlus + b * mMinus) / (s + b) →
        a = s) :=
  payoff_le_of_eq_max_sqrt hb ha hs

example {mMinus mPlus b s : ℝ} (hb : 0 < b)
    (hs : s = max 0 (Real.sqrt (b * (mPlus - mMinus)) - b)) :
    (s + b) ^ 2 = b * (mPlus - mMinus) ↔ b ≤ mPlus - mMinus :=
  sq_eq_mul_iff_of_eq_max_sqrt hb hs

/-! ## Consequences of the hypotheses: a nonnegative maximiser and positive denominators -/

example {mMinus mPlus b s : ℝ} (hb : 0 < b)
    (hs : s = max 0 (Real.sqrt (b * (mPlus - mMinus)) - b)) : 0 ≤ s ∧ 0 < s + b := by
  have : 0 ≤ s := hs ▸ le_max_left _ _
  exact ⟨this, by linarith⟩

/-! ## The regimes, with `b = 1` -/

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `D = 4 > b = 1`: the maximiser `√4 - 1 = 1` is interior and the equation holds. -/
example : max 0 (Real.sqrt (1 * (4 - 0)) - 1) = (1 : ℝ) := by
  rw [show (1 : ℝ) * (4 - 0) = 4 by norm_num, sqrt_four]
  norm_num

example : ((1 : ℝ) + 1) ^ 2 = 1 * (4 - 0) :=
  (sq_eq_mul_iff_of_eq_max_sqrt one_pos (s := 1) (mMinus := 0) (mPlus := 4) (by
    rw [show (1 : ℝ) * (4 - 0) = 4 by norm_num, sqrt_four]; norm_num)).2 (by norm_num)

/-- `D = b = 1`: the maximiser is `0` and the first-order equation still holds. -/
example : max 0 (Real.sqrt (1 * (1 - 0)) - 1) = (0 : ℝ) := by norm_num

example : ((0 : ℝ) + 1) ^ 2 = 1 * (1 - 0) :=
  (sq_eq_mul_iff_of_eq_max_sqrt one_pos (s := 0) (mMinus := 0) (mPlus := 1) (by norm_num)).2
    (by norm_num)

/-- `0 < D = 1/2 < b = 1`: the maximiser is the corner `0` and the equation fails. -/
example : max 0 (Real.sqrt (1 * (1 / 2 - 0)) - 1) = (0 : ℝ) := by
  have : Real.sqrt (1 * (1 / 2 - 0)) - 1 ≤ 0 := by
    rw [sub_nonpos, Real.sqrt_le_left zero_le_one]; norm_num
  exact max_eq_left this

example (hs : (0 : ℝ) = max 0 (Real.sqrt (1 * (1 / 2 - 0)) - 1)) :
    ¬ ((0 : ℝ) + 1) ^ 2 = 1 * (1 / 2 - 0) := by
  rw [sq_eq_mul_iff_of_eq_max_sqrt one_pos hs]
  norm_num

/-- `D = 0`: the maximiser is `0` and the equation fails. -/
example : max 0 (Real.sqrt (1 * (2 - 2)) - 1) = (0 : ℝ) := by norm_num

example : ¬ ((0 : ℝ) + 1) ^ 2 = 1 * (2 - 2) := by
  rw [sq_eq_mul_iff_of_eq_max_sqrt one_pos (by norm_num)]
  norm_num

/-- `D = -3 < 0`: `Real.sqrt` of the negative number `b D` is `0`, so the maximiser is `0`. -/
example : max 0 (Real.sqrt (1 * (0 - 3)) - 1) = (0 : ℝ) := by
  rw [Real.sqrt_eq_zero_of_nonpos (by norm_num)]
  norm_num

/-! ## Equality and uniqueness, with negative payoffs -/

/-- With `m₋ = -5`, `m₊ = -1` (`D = 4`) and `b = 1` the maximiser is `1`; the stake `2` is
strictly worse, by uniqueness. -/
example :
    -2 + (2 * (-1) + 1 * (-5)) / (2 + 1) < -1 + (1 * (-1) + 1 * (-5)) / (1 + 1 : ℝ) := by
  have hs : (1 : ℝ) = max 0 (Real.sqrt (1 * (-1 - -5)) - 1) := by
    rw [show (1 : ℝ) * (-1 - -5) = 4 by norm_num, sqrt_four]; norm_num
  obtain ⟨hle, huniq⟩ := payoff_le_of_eq_max_sqrt (a := 2) one_pos (by norm_num) hs
  exact lt_of_le_of_ne hle fun h => absurd (huniq h) (by norm_num)

/-- The maximiser attains its own value. -/
example {mMinus mPlus b s : ℝ} (hb : 0 < b)
    (hs : s = max 0 (Real.sqrt (b * (mPlus - mMinus)) - b)) :
    -s + (s * mPlus + b * mMinus) / (s + b) ≤ -s + (s * mPlus + b * mMinus) / (s + b) :=
  (payoff_le_of_eq_max_sqrt hb (hs ▸ le_max_left _ _) hs).1

/-! ## The hypotheses `0 ≤ a` and `0 < b` are needed

These counterexamples concern the totalised real expression (where `x / 0 = 0`). -/

/-- Without `0 ≤ a`: at `b = 1`, `m₋ = 0`, `m₊ = 4` (maximiser `1`, value `1`), the stake
`a = -2` gives the larger value `10`. -/
example : -1 + (1 * 4 + 1 * 0) / (1 + 1 : ℝ) < -(-2) + ((-2) * 4 + 1 * 0) / ((-2) + 1 : ℝ) := by
  norm_num

/-- Without `0 ≤ a`: the stake `a = -1` has the same value `1` as the maximiser `1`. -/
example : -(-1) + ((-1) * 4 + 1 * 0) / ((-1) + 1 : ℝ) = -1 + (1 * 4 + 1 * 0) / (1 + 1 : ℝ) := by
  norm_num

/-- Without `0 < b`: at `b = 0`, `m₋ = 0`, `m₊ = 4`, the formula gives `s = 0` with value `0`,
but the stake `a = 1` gives `3`. -/
example : max 0 (Real.sqrt (0 * (4 - 0)) - 0) = (0 : ℝ) := by norm_num

example : -0 + (0 * 4 + 0 * 0) / (0 + 0 : ℝ) < -1 + (1 * 4 + 0 * 0) / (1 + 0 : ℝ) := by
  norm_num

end MathlibExtTest.Analysis.SpecialFunctions.OneStepPayoffMax

#print axioms payoff_le_of_eq_max_sqrt
#print axioms sq_eq_mul_iff_of_eq_max_sqrt
