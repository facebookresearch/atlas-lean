/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciDivGoldenRatio

/-!
# Tests for Fibonacci numbers divided by the golden ratio

The identity `fib_div_goldenRatio_sub_fib` at `n = 2`, its use to find the integer nearest to
`F_n / φ`, and the two indices below the hypothesis `2 ≤ n`: the identity still holds at `n = 1`
and fails at `n = 0`.
-/

open MetaMathlibExt

-- For `n = 2` the identity reads `F_2 / φ - F_1 = -φ⁻²`; with `φ⁻¹ = φ - 1` this is
-- `φ⁻² = 2 - φ`.
example : Real.goldenRatio ^ (-2 : ℤ) = 2 - Real.goldenRatio := by
  have h := fib_div_goldenRatio_sub_fib 2 le_rfl
  rw [div_eq_mul_inv, Real.inv_goldenRatio] at h
  norm_num at h ⊢
  linarith [Real.goldenRatio_add_goldenConj]

-- Since `0 < φ ^ (-n) ≤ φ⁻² < 1/2` for `n ≥ 2`, `F_{n-1}` is the integer nearest to `F_n / φ`.
example (n : ℕ) (hn : 2 ≤ n) :
    round ((Nat.fib n : ℝ) / Real.goldenRatio) = Nat.fib (n - 1) := by
  have h := fib_div_goldenRatio_sub_fib n hn
  have hpos : 0 < Real.goldenRatio ^ (-(n : ℤ)) := zpow_pos Real.goldenRatio_pos _
  have hsmall : Real.goldenRatio ^ (-(n : ℤ)) < 1 / 2 := by
    calc Real.goldenRatio ^ (-(n : ℤ)) ≤ Real.goldenRatio ^ (-2 : ℤ) :=
          zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
      _ < 1 / 2 := by
        rw [zpow_neg, zpow_ofNat, Real.goldenRatio_sq]
        rw [inv_lt_comm₀ (by linarith [Real.goldenRatio_pos]) (by norm_num)]
        linarith [Real.one_lt_goldenRatio]
  rw [round_eq, Int.floor_eq_iff]
  rcases neg_one_pow_eq_or ℝ (n + 1) with hs | hs <;> rw [hs] at h <;> push_cast <;>
    constructor <;> linarith

-- The source's hypothesis `2 ≤ n` is not sharp: the identity also holds at `n = 1`.
example : (Nat.fib 1 : ℝ) / Real.goldenRatio - Nat.fib (1 - 1) =
    (-1) ^ (1 + 1) * Real.goldenRatio ^ (-((1 : ℕ) : ℤ)) := by
  norm_num [zpow_neg_one]

-- At `n = 0` the statement fails, because `Nat.fib (0 - 1) = Nat.fib 0 = 0` makes the left-hand
-- side `0`, while the right-hand side is `-1`.
example : (Nat.fib 0 : ℝ) / Real.goldenRatio - Nat.fib (0 - 1) ≠
    (-1) ^ (0 + 1) * Real.goldenRatio ^ (-((0 : ℕ) : ℤ)) := by
  norm_num
