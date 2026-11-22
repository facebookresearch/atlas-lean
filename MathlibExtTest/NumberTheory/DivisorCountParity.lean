/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DivisorCountParity
public import MathlibExt.NumberTheory.SquareModEight
public import MathlibExt.NumberTheory.X2Y2Count
public import Mathlib.Tactic.NormNum

/-!
# Tests for divisor-count parity, squares modulo 8, and positive `x^2 + 2y^2` counts

These examples exercise the involution parity lemmas, the divisor-count parity facts, the
character divisor sum modulo 4, the square residues modulo 8 and 16, and the `ℤ[√-2]`
representation-count lemmas promoted from the `DivisorSumSquaresCongruence16n6` proof.
-/

-- `i ↦ 3 - i` is a fixed-point-free involution of `{0, 1, 2, 3}`.
example : Even (Finset.range 4).card :=
  Finset.even_card_of_involution (f := fun i => 3 - i)
    (by intro a ha; simp only [Finset.mem_range] at ha ⊢; omega)
    (by intro a ha; simp only [Finset.mem_range] at ha; omega)
    (by intro a ha; simp only [Finset.mem_range] at ha; omega)

example : ((∑ k ∈ Finset.range 3, 2 * k) / 2) % 2
    = ((Finset.range 3).filter (fun k => 2 * k % 4 = 2)).card % 2 :=
  Finset.sum_div_two_mod_two_eq_card_filter _ _ (fun k _ => even_two_mul k)

-- Divisor counts.
example : (Nat.divisors (2 * 15)).card = 2 * (Nat.divisors 15).card :=
  Nat.card_divisors_two_mul_of_odd ⟨7, by norm_num⟩

example : Even (Nat.divisors 11).card :=
  Nat.even_card_divisors_of_not_isSquare (Nat.not_isSquare_of_mod_eight_eq_three (by norm_num))

example : Odd (Nat.divisors 9).card :=
  (Nat.odd_card_divisors_iff_isSquare (by norm_num)).mpr ⟨3, by norm_num⟩

example : 36 / (36 / 4) = 4 :=
  Nat.div_div_self_of_mem_divisors (Nat.mem_divisors.mpr ⟨⟨9, rfl⟩, by norm_num⟩)

-- Character values on odd arguments.
example : ZMod.χ₄ (7 : ℕ) = 1 ∨ ZMod.χ₄ (7 : ℕ) = -1 :=
  ZMod.χ₄_nat_eq_one_or_neg_one_of_odd ⟨3, by norm_num⟩

-- `11 ≡ 3 mod 8` is a nonsquare with `χ₈' 11 = 1`: the divisor sum `1 + 1` and the divisor
-- count `2` agree mod 4.
example : (∑ d ∈ Nat.divisors 11, ZMod.χ₈' d) % 4 = ((Nat.divisors 11).card : ℤ) % 4 :=
  MulChar.sum_divisors_emod_four_eq_card ZMod.χ₈'
    (fun _ hd => ZMod.χ₈'_nat_eq_one_or_neg_one_of_odd
      (Odd.of_dvd_nat (⟨5, by norm_num⟩ : Odd 11) (Nat.dvd_of_mem_divisors hd)))
    (by rw [ZMod.χ₈'_nat_eq_if_mod_eight]; norm_num)
    (Nat.not_isSquare_of_mod_eight_eq_three (by norm_num))

-- Squares modulo 8 and 16.
example (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := Nat.sq_mod_eight n

example (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := Int.sq_emod_eight x

example : ¬ IsSquare 14 := Nat.not_isSquare_of_mod_eight_eq_six (by norm_num)

example : ¬ IsSquare (22 - 3 ^ 2) :=
  Nat.not_isSquare_sub_sq_of_mod_eight_eq_six (by norm_num) (by norm_num)

example : 5 ^ 2 % 16 = 9 ∧ (5 % 8 = 3 ∨ 5 % 8 = 5) := by
  rcases Nat.sq_mod_sixteen_of_odd 5 ⟨2, by norm_num⟩ with h | h
  · norm_num at h
  · exact h

-- `ℤ[√-2]` counts.
open SumSquares in
example : divChiNeg2Sum (2 * 3) = divChiNeg2Sum 3 := divChiNeg2Sum_two_mul_of_odd ⟨1, rfl⟩

open SumSquares in
example {z : Zsqrtd (-2 : ℤ)} (hz : (Zsqrtd.norm z).natAbs = 3) :
    z.re * z.re + 2 * (z.im * z.im) = 3 :=
  re_mul_re_add_two_mul_im_mul_im hz

open SumSquares in
example (N : ℕ)
    (hre : ∀ z : Zsqrtd (-2 : ℤ), (Zsqrtd.norm z).natAbs = N → z.re ≠ 0)
    (him : ∀ z : Zsqrtd (-2 : ℤ), (Zsqrtd.norm z).natAbs = N → z.im ≠ 0) :
    repX2Y2Count N = 4 * ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun p : ℕ × ℕ => p.1 ^ 2 + 2 * p.2 ^ 2 = N ∧ 0 < p.1 ∧ 0 < p.2)).card :=
  repX2Y2Count_eq_four_mul_pos N hre him

#print axioms MulChar.sum_divisors_emod_four_eq_card
#print axioms SumSquares.repX2Y2Count_eq_four_mul_pos
