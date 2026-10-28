/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedIntegerUniqueness

/-! Exact original-coordinate identities for sixteen-bit words with spare upper bits. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- One original signed coordinate stored with bias256 in a sixteen-bit slot. -/
def generatedRootEightPackedWideBiasedDigit (w : ℕ) (i : Fin 16) : ℤ :=
  ((w / 65536 ^ i.val % 65536 : ℕ) : ℤ) - 256

/-- The entire original signed polynomial, subtracting the bias from every slot. -/
def generatedRootEightPackedWideBiasedWord (w : ℕ) : ℤ :=
  (w : ℤ) - 256 * ∑ i : Fin 16, (65536 : ℤ) ^ i.val

/-- All unused upper bits in every original sixteen-bit slot. -/
def generatedRootEightPackedWideUpperMask : ℕ := 114889216610471477702331269233309262535302166520158877486864880484177055645184

private theorem upper_mask_digits : ∀ i : Fin 16,
    generatedRootEightPackedWideUpperMask / 65536 ^ i.val % 65536 = 65024 := by
  decide +kernel

/-- The whole biased word is exactly the polynomial of all sixteen original signed coordinates. -/
theorem generatedRootEight_packed_wide_biased_word (w : ℕ) (hw : w < 65536 ^ 16) :
    (∑ i : Fin 16, generatedRootEightPackedWideBiasedDigit w i * (65536 : ℤ) ^ i.val) =
      generatedRootEightPackedWideBiasedWord w := by
  have hn := generatedRootEight_packed_natural_digits 65536 w 16
  rw [Nat.mod_eq_of_lt hw] at hn
  have hnc := congrArg (fun n : ℕ => (n : ℤ)) hn
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnc
  unfold generatedRootEightPackedWideBiasedDigit generatedRootEightPackedWideBiasedWord
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnc]

/-- A complete unused-bit certificate gives the exact universal bound on every original signed digit. -/
theorem generatedRootEight_packed_wide_biased_digit_abs (w : ℕ)
    (hu : w &&& generatedRootEightPackedWideUpperMask = 0) (i : Fin 16) :
    |generatedRootEightPackedWideBiasedDigit w i| ≤ 256 := by
  let a := w / 65536 ^ i.val % 65536
  have ha : a < 65536 := Nat.mod_lt _ (by decide)
  have hp : 65536 ^ i.val = 2 ^ (16 * i.val) := by rw [pow_mul]; norm_num
  have hz := congrArg (fun z : ℕ => z / 2 ^ (16 * i.val) % 2 ^ 16) hu
  simp only [Nat.and_div_two_pow, Nat.and_mod_two_pow, Nat.zero_div, Nat.zero_mod] at hz
  have hm := upper_mask_digits i
  rw [hp] at hm
  rw [hm] at hz
  change (w / 2 ^ (16 * i.val) % 65536) &&& 65024 = 0 at hz
  rw [← hp] at hz
  change a &&& 65024 = 0 at hz
  have hb := congrArg (fun z : ℕ => z / 2 ^ 9) hz
  rw [Nat.and_div_two_pow] at hb
  change (a / 512) &&& 127 = 0 at hb
  have hseven : 127 = 2 ^ 7 - 1 := by decide
  rw [hseven, Nat.and_two_pow_sub_one_eq_mod] at hb
  have hd : a / 512 < 128 := by omega
  change (a / 512) % 128 = 0 at hb
  rw [Nat.mod_eq_of_lt hd] at hb
  have hsmall : a < 512 := by omega
  unfold generatedRootEightPackedWideBiasedDigit
  change |(a : ℤ) - 256| ≤ 256
  apply abs_le.mpr
  constructor <;> omega

/-- A complete bounded linear word equation implies every original coordinate equation. -/
theorem generatedRootEight_packed_wide_biased_linear {k : ℕ} (w : Fin k → ℕ) (t : ℕ)
    (c : Fin k → ℤ) (a : ℤ)
    (hw : ∀ j, w j < 65536 ^ 16) (ht : t < 65536 ^ 16)
    (hb : ∀ i : Fin 16,
      |(∑ j : Fin k, c j * generatedRootEightPackedWideBiasedDigit (w j) i) -
        a * generatedRootEightPackedWideBiasedDigit t i| < 65536)
    (he : (∑ j : Fin k, c j * generatedRootEightPackedWideBiasedWord (w j)) =
      a * generatedRootEightPackedWideBiasedWord t) :
    ∀ i : Fin 16, (∑ j : Fin k, c j * generatedRootEightPackedWideBiasedDigit (w j) i) =
      a * generatedRootEightPackedWideBiasedDigit t i := by
  let f : Fin 16 → ℤ := fun i =>
    (∑ j : Fin k, c j * generatedRootEightPackedWideBiasedDigit (w j) i) -
      a * generatedRootEightPackedWideBiasedDigit t i
  have hp : (∑ i : Fin 16, f i * (65536 : ℤ) ^ i.val) = 0 := by
    calc
      _ = (∑ j : Fin k, c j * (∑ i : Fin 16,
          generatedRootEightPackedWideBiasedDigit (w j) i * (65536 : ℤ) ^ i.val)) -
        a * (∑ i : Fin 16, generatedRootEightPackedWideBiasedDigit t i * (65536 : ℤ) ^ i.val) := by
          dsimp [f]
          simp_rw [sub_mul, Finset.sum_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_comm]
          simp only [Finset.mul_sum, mul_assoc]
      _ = 0 := by
        simp_rw [generatedRootEight_packed_wide_biased_word _ (hw _),
          generatedRootEight_packed_wide_biased_word t ht]
        exact sub_eq_zero.mpr he
  have hz := generatedRootEight_packed_integer_zero 65536 (by norm_num) f hb hp
  intro i
  exact sub_eq_zero.mp (hz i)

/-- All original coordinates follow from a whole-word equation with exact coefficient budget. -/
theorem generatedRootEight_packed_wide_biased_bounded {k : ℕ} (w : Fin k → ℕ) (t : ℕ)
    (c : Fin k → ℤ) (a : ℤ)
    (hc : (∑ j : Fin k, |c j|) + |a| < 256)
    (hw : ∀ j, w j < 65536 ^ 16) (ht : t < 65536 ^ 16)
    (hu : ∀ j, w j &&& generatedRootEightPackedWideUpperMask = 0)
    (htu : t &&& generatedRootEightPackedWideUpperMask = 0)
    (he : (∑ j : Fin k, c j * generatedRootEightPackedWideBiasedWord (w j)) =
      a * generatedRootEightPackedWideBiasedWord t) :
    ∀ i : Fin 16, (∑ j : Fin k, c j * generatedRootEightPackedWideBiasedDigit (w j) i) =
      a * generatedRootEightPackedWideBiasedDigit t i := by
  apply generatedRootEight_packed_wide_biased_linear w t c a hw ht
  · intro i
    have hs : |∑ j : Fin k, c j * generatedRootEightPackedWideBiasedDigit (w j) i| ≤
        (∑ j : Fin k, |c j|) * 256 := by
      calc
        _ ≤ ∑ j : Fin k, |c j * generatedRootEightPackedWideBiasedDigit (w j) i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin k, |c j| * 256 := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (generatedRootEight_packed_wide_biased_digit_abs _ (hu j) i) (abs_nonneg _)
        _ = (∑ j : Fin k, |c j|) * 256 := by rw [Finset.sum_mul]
    have htarget : |a * generatedRootEightPackedWideBiasedDigit t i| ≤ |a| * 256 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (generatedRootEight_packed_wide_biased_digit_abs _ htu i) (abs_nonneg _)
    have hb := abs_sub_le (∑ j : Fin k, c j * generatedRootEightPackedWideBiasedDigit (w j) i)
      0 (a * generatedRootEightPackedWideBiasedDigit t i)
    simp only [sub_zero, zero_sub, abs_neg] at hb
    linarith
  · exact he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
