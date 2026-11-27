/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusFixedPointInterval

open MetaMathlibExt

namespace JosephusFixedPointIntervalTest

private instance decidableFixedPoint : DecidablePred IsJosephusThreeFixedPoint :=
  fun n => inferInstanceAs (Decidable (1 ≤ n ∧ josephus 3 n = n))

-- The first three fixed points of `J₃` are `1`, `2` and `13`.
private theorem nth_zero : Nat.nth IsJosephusThreeFixedPoint 0 = 1 :=
  Nat.nth_count (p := IsJosephusThreeFixedPoint) (n := 1) (by decide)

private theorem nth_one : Nat.nth IsJosephusThreeFixedPoint 1 = 2 :=
  Nat.nth_count (p := IsJosephusThreeFixedPoint) (n := 2) (by decide)

private theorem nth_two : Nat.nth IsJosephusThreeFixedPoint 2 = 13 :=
  Nat.nth_count (p := IsJosephusThreeFixedPoint) (n := 13) (by decide)

-- The valuations `ν₂(3a + 2)` at the fixed points `a = 1` and `a = 2`.
private theorem padicValNat_five : padicValNat 2 5 = 0 := by
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd (by decide)

private theorem padicValNat_eight : padicValNat 2 8 = 3 := by
  rw [Nat.padicValNat_def]
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.multiplicity_prime_pow (p := 2) 3

-- On the first interval `[2, 2]` the valuation `ν₂(5)` and the logarithm `log_{3/2} 1` vanish,
-- so the formula reads `J₃(2) = 7 - 5`.
example : josephus 3 2 = 2 := by
  have h := josephusThree_eq_of_mem_fixedPoint_interval 0 2 (by rw [nth_zero]) (by rw [nth_one])
  rw [nth_zero, nth_one] at h
  norm_num [padicValNat_five] at h
  exact_mod_cast h

-- At the left end `3` of `[3, 13]` the logarithm `log_{3/2}(7/8)` is negative with ceiling `0`,
-- so the exponent is the whole valuation `ν₂(8) = 3` and `J₃(3) = 10 - (2/3)^3 · 27`.
example : josephus 3 3 = 2 := by
  have h := josephusThree_eq_of_mem_fixedPoint_interval 1 3 (by rw [nth_one])
    (by rw [nth_two]; decide)
  rw [nth_one, nth_two] at h
  have hc : ⌈Real.logb (3 / 2) (7 / 8 : ℝ)⌉ = 0 := by
    rw [Int.ceil_eq_iff, Int.cast_zero, zero_sub]
    constructor
    · rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num), Real.rpow_neg_one]
      norm_num
    · exact Real.logb_nonpos (by norm_num) (by norm_num) (by norm_num)
  norm_num [padicValNat_eight, hc] at h
  exact_mod_cast h

-- Just after the pure high extremal point `8`, `log_{3/2}(19/8)` lies in `(2, 3]`, the ceiling
-- jumps to `3`, and the survivor wraps around: `J₃(9) = 28 - 27`.
example : josephus 3 9 = 1 := by
  have h := josephusThree_eq_of_mem_fixedPoint_interval 1 9 (by rw [nth_one]; decide)
    (by rw [nth_two]; decide)
  rw [nth_one, nth_two] at h
  have hc : ⌈Real.logb (3 / 2) (19 / 8 : ℝ)⌉ = 3 := by
    rw [Int.ceil_eq_iff]
    constructor
    · rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num),
        show ((3 : ℤ) : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    · rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num),
        show ((3 : ℤ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
  norm_num [padicValNat_eight, hc] at h
  exact_mod_cast h

-- At the right end `13` the logarithm `log_{3/2}(27/8) = 3` is an integer, the exponent is `0`,
-- and the formula returns the next fixed point: `J₃(13) = 40 - 27`.
example : josephus 3 13 = 13 := by
  have h := josephusThree_eq_of_mem_fixedPoint_interval 1 13 (by rw [nth_one]; decide)
    (by rw [nth_two])
  rw [nth_one, nth_two] at h
  have hc : ⌈Real.logb (3 / 2) (27 / 8 : ℝ)⌉ = 3 := by
    rw [show (27 / 8 : ℝ) = (3 / 2) ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
      Real.logb_rpow (by norm_num) (by norm_num), Int.ceil_natCast]
    rfl
  norm_num [padicValNat_eight, hc] at h
  exact_mod_cast h

end JosephusFixedPointIntervalTest
