/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.NumberTheory.FermatQuotient
import Mathlib.Tactic.NormNum.Prime

-- Small exact values via the public evaluation theorem.

example : Int.fermatQuotient 3 (by decide) (2 : ℤ) (by decide) = 1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 5 (by decide) (2 : ℤ) (by decide) = 3 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 3 (by decide) (4 : ℤ) (by decide) = 5 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Evaluation lemma is definitionally `rfl`.
example : Int.fermatQuotient 5 (by decide) (2 : ℤ) (by decide) =
    ((2 : ℤ) ^ (4 : ℕ) - 1) / (5 : ℤ) :=
  Int.fermatQuotient_eq 5 (by decide) (2 : ℤ) (by decide)

-- Source-motivated specialization at `a = 2` for an odd prime.
example : Int.fermatQuotient 7 (by decide) (2 : ℤ) (by decide) = 9 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Boundary prime `p = 2`.
example : Int.fermatQuotient 2 (by decide) (3 : ℤ) (by decide) = 1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 2 (by decide) (-1 : ℤ) (by decide) = -1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Negative integer input with odd prime.
example : Int.fermatQuotient 3 (by decide) (-2 : ℤ) (by decide) = 1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 5 (by decide) (-2 : ℤ) (by decide) = 3 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Public recovery theorem applied on concrete cases.
example : (3 : ℤ) * Int.fermatQuotient 3 (by decide) (2 : ℤ) (by decide) =
    (2 : ℤ) ^ (2 : ℕ) - 1 :=
  Int.natCast_mul_fermatQuotient 3 (by decide) (2 : ℤ) (by decide)

example : (5 : ℤ) * Int.fermatQuotient 5 (by decide) (2 : ℤ) (by decide) =
    (2 : ℤ) ^ (4 : ℕ) - 1 :=
  Int.natCast_mul_fermatQuotient 5 (by decide) (2 : ℤ) (by decide)

/-! ### Congruences modulo `p` -/

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- `q_5(6) = 259 ≡ q_5(2) + q_5(3) = 3 + 16 (mod 5)`, checked by hand and from the theorem.
example : Int.fermatQuotient 5 (by decide) (6 : ℤ) (by decide) = 259 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 5 (by decide) (2 * 3 : ℤ) (by decide) ≡
    Int.fermatQuotient 5 (by decide) 2 (by decide) +
      Int.fermatQuotient 5 (by decide) 3 (by decide) [ZMOD 5] :=
  Int.fermatQuotient_mul_modEq 5 (by decide) (by decide) (by decide)

-- `q_5(2 + 5) ≡ q_5(2) - 3 · 1 (mod 5)` with `2 · 3 ≡ 1 (mod 5)`; here `q_5(7) = 480`.
example : Int.fermatQuotient 5 (by decide) (2 + 5 * 1 : ℤ) (by decide) ≡
    Int.fermatQuotient 5 (by decide) 2 (by decide) - 3 * 1 [ZMOD 5] :=
  Int.fermatQuotient_add_mul_modEq 5 (by decide) 1 (by decide) (by decide) (by decide)

example : Int.fermatQuotient 5 (by decide) (7 : ℤ) (by decide) = 480 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

/-! ### Lerch's formula -/

-- `p = 3`, `a = 2`: `2 q_3(2) = 2 ≡ 1⁻¹ ⌊2/3⌋ + 2⁻¹ ⌊4/3⌋ = 0 + 2 (mod 3)`.
example : ((2 : ℕ) : ZMod 3) * (Int.fermatQuotient 3 (by decide) ((2 : ℕ) : ℤ) (by decide) : ZMod 3) =
    ∑ j ∈ Finset.Icc 1 (3 - 1), ((j : ℕ) : ZMod 3)⁻¹ * ((2 * j / 3 : ℕ) : ZMod 3) :=
  Int.natCast_mul_fermatQuotient_eq_sum 3 (by decide)

example : ∑ j ∈ Finset.Icc 1 (3 - 1), ((j : ℕ) : ZMod 3)⁻¹ * ((2 * j / 3 : ℕ) : ZMod 3) = 2 := by
  have i2 : (2 : ZMod 3)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide)
  rw [show Finset.Icc 1 (3 - 1) = {1, 2} by rfl]
  simp [i2]

-- `p = 5`, `a = 3`: `3 q_5(3) = 3 · 16 = 48 ≡ 3 (mod 5)`, and Lerch's sum is also `3`.
example : Int.fermatQuotient 5 (by decide) (3 : ℤ) (by decide) = 16 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : ((3 : ℕ) : ZMod 5) * (Int.fermatQuotient 5 (by decide) ((3 : ℕ) : ℤ) (by decide) : ZMod 5)
    = 3 := by
  rw [Int.natCast_mul_fermatQuotient_eq_sum 5 (by decide)]
  have i2 : (2 : ZMod 5)⁻¹ = 3 := inv_eq_of_mul_eq_one_right (by decide)
  have i3 : (3 : ZMod 5)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide)
  have i4 : (4 : ZMod 5)⁻¹ = 4 := inv_eq_of_mul_eq_one_right (by decide)
  rw [show Finset.Icc 1 (5 - 1) = {1, 2, 3, 4} by rfl]
  simp [i2, i3, i4]
  decide

-- Lerch's formula also holds at `p = 2`: `3 q_2(3) = 3 ≡ ⌊3/2⌋ = 1 (mod 2)`.
example : ((3 : ℕ) : ZMod 2) * (Int.fermatQuotient 2 (by decide) ((3 : ℕ) : ℤ) (by decide) : ZMod 2) =
    1 := by
  rw [Int.natCast_mul_fermatQuotient_eq_sum 2 (by decide)]
  rw [show Finset.Icc 1 (2 - 1) = {1} by rfl]
  simp

/-! ### `q_p(2)` and the Wieferich criterion -/

-- `q_3(2) = 1 ≡ 1/2 - 1/4 (mod 3)`.
example : (Int.fermatQuotient 3 (by decide) 2 (by decide) : ZMod 3) =
    ∑ j ∈ Finset.Icc (1 : ℕ) (3 - 1), (-1 : ZMod 3) ^ (j + 1) / (2 * (j : ZMod 3)) :=
  Int.fermatQuotient_two_eq_sum 3 (by decide)

-- `q_5(2) = 3 ≡ 1/2 - 1/4 + 1/6 - 1/8 (mod 5)`, checked by hand.
example : ∑ j ∈ Finset.Icc (1 : ℕ) (5 - 1), (-1 : ZMod 5) ^ (j + 1) / (2 * (j : ZMod 5)) = 3 := by
  have i2 : (2 : ZMod 5)⁻¹ = 3 := inv_eq_of_mul_eq_one_right (by decide)
  have i3 : (3 : ZMod 5)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide)
  have i4 : (4 : ZMod 5)⁻¹ = 4 := inv_eq_of_mul_eq_one_right (by decide)
  rw [show Finset.Icc (1 : ℕ) (5 - 1) = {1, 2, 3, 4} by rfl]
  simp [div_eq_mul_inv, i2, i3, i4]
  decide

-- The coprimality hypothesis of `fermatQuotient_two_eq_sum` excludes `p = 2`.
example : ¬ IsCoprime (2 : ℤ) ((2 : ℕ) : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]; decide

-- `p = 3`: `1 - 1/2 = 1/2` has numerator `1`, and `2 ^ 2 ≢ 1 (mod 9)`.
example : ¬ ((3 : ℕ) : ℤ) ∣ (∑ j ∈ Finset.Icc (1 : ℕ) (3 - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))).num := by
  rw [← Int.two_pow_modEq_one_sq_iff_dvd_num_alternating 3 (by decide)]
  decide

example : (∑ j ∈ Finset.Icc (1 : ℕ) (3 - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))) = 1 / 2 := by
  rw [show Finset.Icc (1 : ℕ) (3 - 1) = {1, 2} by rfl, Finset.sum_pair (by decide)]
  norm_num

-- `p = 1093`, the first Wieferich prime: the criterion forces `1093` to divide the numerator.
set_option exponentiation.threshold 2048 in
example : (1093 : ℤ) ∣
    (∑ j ∈ Finset.Icc (1 : ℕ) (1093 - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))).num := by
  have hp : Nat.Prime 1093 := by norm_num
  have h := (Nat.isWieferichPrime_iff_dvd_num_alternating hp).mp
    ((Nat.isWieferichPrime_iff_mod 1093).mpr ⟨hp, by decide⟩)
  exact_mod_cast h

-- The criterion covers `p = 2`, where both sides are false.
example : ¬ Nat.IsWieferichPrime 2 ∧
    ¬ (2 : ℤ) ∣ (∑ j ∈ Finset.Icc (1 : ℕ) (2 - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))).num := by
  have hW : ¬ Nat.IsWieferichPrime 2 := by norm_num [Nat.IsWieferichPrime]
  exact ⟨hW, fun h2 =>
    hW ((Nat.isWieferichPrime_iff_dvd_num_alternating Nat.prime_two).mpr (by exact_mod_cast h2))⟩

example : ¬ (2 : ℤ) ^ (2 - 1) ≡ 1 [ZMOD ((2 : ℕ) : ℤ) ^ 2] ∧
    ¬ ((2 : ℕ) : ℤ) ∣ (∑ j ∈ Finset.Icc (1 : ℕ) (2 - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))).num := by
  rw [← Int.two_pow_modEq_one_sq_iff_dvd_num_alternating 2 Nat.prime_two, and_self]
  decide
