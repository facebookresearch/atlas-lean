/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WesleyFractionalConstant

/-!
# Tests for Wesley's constants and the fractional parts of $(F_n + \varepsilon)/\sqrt{5}$

Values of `wesleyFractionalConstant` in each residue class, both parts of
`fract_fib_add_div_sqrt_five` at concrete indices, a direct computation of one integer part, and
a small index where the formula for the fractional part fails.
-/

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.WesleyFractionalConstant

/-! ### Values of the constants -/

-- For `ε = 0` the constant is `(L_n mod 5) / 5`, with Lucas residues `2, 1, 3, 4` modulo `5`.
example : wesleyFractionalConstant 16 0 = 2 / 5 :=
  wesleyFractionalConstant_zero_of_mod_four_eq_zero (by decide)

example : wesleyFractionalConstant 13 0 = 1 / 5 := by norm_num [wesleyFractionalConstant]

example : wesleyFractionalConstant 14 0 = 3 / 5 := by norm_num [wesleyFractionalConstant]

example : wesleyFractionalConstant 15 0 = 4 / 5 := by norm_num [wesleyFractionalConstant]

-- The two special cases `ε = -4` with `n ≡ 1, 3 (mod 4)`.
example : wesleyFractionalConstant 13 (-4) = (11 - 4 * √5) / 5 := by
  norm_num [wesleyFractionalConstant]

example : wesleyFractionalConstant 15 (-4) = (9 - 4 * √5) / 5 := by
  norm_num [wesleyFractionalConstant]

-- A generic case: `c_{n,4} = {3/5 + 4/√5} = (4√5 - 7)/5` for `n ≡ 2 (mod 4)`.
example : wesleyFractionalConstant 14 4 = (4 * √5 - 7) / 5 := by
  norm_num [wesleyFractionalConstant]; ring

-- The smallest constant of the lemma, `c_{n,-4} = (9 - 4√5)/5 ≈ 0.011` for `n ≡ 3 (mod 4)`.
example : 0 < wesleyFractionalConstant 15 (-4) ∧ wesleyFractionalConstant 15 (-4) < 1 / 50 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  norm_num [wesleyFractionalConstant]
  constructor <;> nlinarith

/-! ### The lemma at concrete indices -/

-- Part (ii) for `n = 13 ≡ 1 (mod 12)` and `ε = 0`: the integer part is even.
example : Even ⌊((Nat.fib 13 : ℝ) + ((0 : ℤ) : ℝ)) / (2 * Real.goldenRatio - 1)⌋ :=
  (fract_fib_add_div_sqrt_five 13 le_rfl 0 (by decide)).2.mpr (by decide)

-- The same integer part computed directly: `⌊233 / √5⌋ = 104`.
example : ⌊((Nat.fib 13 : ℝ) + ((0 : ℤ) : ℝ)) / (2 * Real.goldenRatio - 1)⌋ = 104 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  have hden : 2 * Real.goldenRatio - 1 = √5 := by simp only [Real.goldenRatio]; ring
  have h5 : (0 : ℝ) < √5 := by positivity
  have hfib : Nat.fib 13 = 233 := by decide
  rw [hden, hfib, Int.floor_eq_iff, le_div_iff₀ h5, div_lt_iff₀ h5]
  norm_num
  constructor <;> nlinarith

-- Part (ii) for `n = 16 ≡ 4 (mod 12)` and `ε = 4`: the integer part is odd.
example : ¬ Even ⌊((Nat.fib 16 : ℝ) + ((4 : ℤ) : ℝ)) / (2 * Real.goldenRatio - 1)⌋ := by
  rw [(fract_fib_add_div_sqrt_five 16 (by norm_num) 4 (by decide)).2]
  decide

-- Part (i) for `n = 15` and `ε = -4`, with the value of the constant substituted.
example : Int.fract (((Nat.fib 15 : ℝ) + ((-4 : ℤ) : ℝ)) / (2 * Real.goldenRatio - 1)) =
    -(2 * (-Real.goldenRatio) ^ (-((15 : ℕ) : ℤ)) / 5) + (9 - 4 * √5) / 5 := by
  rw [(fract_fib_add_div_sqrt_five 15 (by norm_num) (-4) (by decide)).1]
  norm_num [wesleyFractionalConstant]

/-! ### A small index -/

-- For `n = 5` and `ε = 4` the right-hand side of part (i) is `(9√5 - 15)/5 > 1`.
private lemma one_lt_rhs_five :
    1 < -(2 * (-Real.goldenRatio) ^ (-((5 : ℕ) : ℤ)) / 5) + wesleyFractionalConstant 5 4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  have hpow : (-Real.goldenRatio) ^ (-((5 : ℕ) : ℤ)) = Real.goldenConj ^ 5 := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, Real.inv_goldenRatio, neg_neg]
  have h5 : Real.goldenConj ^ 5 = 5 * Real.goldenConj + 3 := by
    have := Real.goldenConj_mul_fib_succ_add_fib 4
    norm_num [Nat.fib_add_two] at this
    linarith
  rw [hpow, h5]
  norm_num [wesleyFractionalConstant, Real.goldenConj]
  nlinarith

-- So part (i) fails at `n = 5`, `ε = 4`: the lemma needs a lower bound on `n`.
example : Int.fract (((Nat.fib 5 : ℝ) + ((4 : ℤ) : ℝ)) / (2 * Real.goldenRatio - 1)) ≠
    -(2 * (-Real.goldenRatio) ^ (-((5 : ℕ) : ℤ)) / 5) + wesleyFractionalConstant 5 4 :=
  fun h => (Int.fract_lt_one _).not_ge (h ▸ one_lt_rhs_five.le)

end MathlibExtTest.NumberTheory.WesleyFractionalConstant
