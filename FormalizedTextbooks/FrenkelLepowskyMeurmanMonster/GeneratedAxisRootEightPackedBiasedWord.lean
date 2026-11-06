/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedIntegerUniqueness

/-! Exact original-coordinate identities for twelve-bit words with spare upper bits. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- One original signed coordinate stored with bias256 in a twelve-bit slot. -/
def generatedRootEightPackedBiasedDigit (w : ℕ) (i : Fin 16) : ℤ :=
  ((w / 4096 ^ i.val % 4096 : ℕ) : ℤ) - 256

/-- The entire original signed polynomial, subtracting the bias from every slot. -/
def generatedRootEightPackedBiasedWord (w : ℕ) : ℤ :=
  (w : ℤ) - 256 * ∑ i : Fin 16, (4096 : ℤ) ^ i.val

/-- All unused upper bits in every original twelve-bit slot. -/
def generatedRootEightPackedUpperMask : ℕ := 5493805279517915471938331939627906333409241004385616530944

private theorem upper_mask_digits : ∀ i : Fin 16,
    generatedRootEightPackedUpperMask / 4096 ^ i.val % 4096 = 3584 := by
  decide +kernel

/-- The whole biased word is exactly the polynomial of all sixteen original signed coordinates. -/
theorem generatedRootEight_packed_biased_word (w : ℕ) (hw : w < 4096 ^ 16) :
    (∑ i : Fin 16, generatedRootEightPackedBiasedDigit w i * (4096 : ℤ) ^ i.val) =
      generatedRootEightPackedBiasedWord w := by
  have hn := generatedRootEight_packed_natural_digits 4096 w 16
  rw [Nat.mod_eq_of_lt hw] at hn
  have hnc := congrArg (fun n : ℕ => (n : ℤ)) hn
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnc
  unfold generatedRootEightPackedBiasedDigit generatedRootEightPackedBiasedWord
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnc]

/-- A complete unused-bit certificate gives the exact universal bound on every original signed digit. -/
theorem generatedRootEight_packed_biased_digit_abs (w : ℕ)
    (hu : w &&& generatedRootEightPackedUpperMask = 0) (i : Fin 16) :
    |generatedRootEightPackedBiasedDigit w i| ≤ 256 := by
  let a := w / 4096 ^ i.val % 4096
  have ha : a < 4096 := Nat.mod_lt _ (by decide)
  have hp : 4096 ^ i.val = 2 ^ (12 * i.val) := by rw [pow_mul]; norm_num
  have hz := congrArg (fun z : ℕ => z / 2 ^ (12 * i.val) % 2 ^ 12) hu
  simp only [Nat.and_div_two_pow, Nat.and_mod_two_pow, Nat.zero_div, Nat.zero_mod] at hz
  have hm := upper_mask_digits i
  rw [hp] at hm
  rw [hm] at hz
  change (w / 2 ^ (12 * i.val) % 4096) &&& 3584 = 0 at hz
  rw [← hp] at hz
  change a &&& 3584 = 0 at hz
  have hb := congrArg (fun z : ℕ => z / 2 ^ 9) hz
  rw [Nat.and_div_two_pow] at hb
  change (a / 512) &&& 7 = 0 at hb
  have hseven : 7 = 2 ^ 3 - 1 := by decide
  rw [hseven, Nat.and_two_pow_sub_one_eq_mod] at hb
  have hd : a / 512 < 8 := by omega
  change (a / 512) % 8 = 0 at hb
  rw [Nat.mod_eq_of_lt hd] at hb
  have hsmall : a < 512 := by omega
  unfold generatedRootEightPackedBiasedDigit
  change |(a : ℤ) - 256| ≤ 256
  apply abs_le.mpr
  constructor <;> omega

/-- A complete bounded linear word equation implies every original coordinate equation. -/
theorem generatedRootEight_packed_biased_linear {k : ℕ} (w : Fin k → ℕ) (t : ℕ)
    (c : Fin k → ℤ) (a : ℤ)
    (hw : ∀ j, w j < 4096 ^ 16) (ht : t < 4096 ^ 16)
    (hb : ∀ i : Fin 16,
      |(∑ j : Fin k, c j * generatedRootEightPackedBiasedDigit (w j) i) -
        a * generatedRootEightPackedBiasedDigit t i| < 4096)
    (he : (∑ j : Fin k, c j * generatedRootEightPackedBiasedWord (w j)) =
      a * generatedRootEightPackedBiasedWord t) :
    ∀ i : Fin 16, (∑ j : Fin k, c j * generatedRootEightPackedBiasedDigit (w j) i) =
      a * generatedRootEightPackedBiasedDigit t i := by
  let f : Fin 16 → ℤ := fun i =>
    (∑ j : Fin k, c j * generatedRootEightPackedBiasedDigit (w j) i) -
      a * generatedRootEightPackedBiasedDigit t i
  have hp : (∑ i : Fin 16, f i * (4096 : ℤ) ^ i.val) = 0 := by
    calc
      _ = (∑ j : Fin k, c j * (∑ i : Fin 16,
          generatedRootEightPackedBiasedDigit (w j) i * (4096 : ℤ) ^ i.val)) -
        a * (∑ i : Fin 16, generatedRootEightPackedBiasedDigit t i * (4096 : ℤ) ^ i.val) := by
          dsimp [f]
          simp_rw [sub_mul, Finset.sum_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_comm]
          simp only [Finset.mul_sum, mul_assoc]
      _ = 0 := by
        simp_rw [generatedRootEight_packed_biased_word _ (hw _),
          generatedRootEight_packed_biased_word t ht]
        exact sub_eq_zero.mpr he
  have hz := generatedRootEight_packed_integer_zero 4096 (by norm_num) f hb hp
  intro i
  exact sub_eq_zero.mp (hz i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
