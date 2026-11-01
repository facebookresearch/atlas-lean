/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedLinear

/-! Full bounded four-term Fourier implications for every original signed slot. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- All three original low bits in all sixteen original slots. -/
def generatedRootEightPackedGapEightMask : ℕ := 305489660253844152623776962639018650766855

private theorem gap_eight_mask_digits : ∀ i : Fin 16,
    generatedRootEightPackedGapEightMask / 2 ^ (9 * i.val) % 2 ^ 3 = 7 := by
  decide +kernel

/-- Every original signed nine-bit digit has its exact universal integral bound. -/
theorem generatedRootEight_packed_signed_digit_abs (w : ℕ) (i : Fin 16) :
    |generatedRootEightPackedSignedDigit w i| ≤ 256 := by
  have ha : w / 512 ^ i.val % 512 < 512 := Nat.mod_lt _ (by decide)
  dsimp only [generatedRootEightPackedSignedDigit]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> omega

/-- A complete word gap certificate implies divisibility of every original signed coordinate. -/
theorem generatedRootEight_packed_signed_digit_eight (w : ℕ)
    (hgap : w &&& generatedRootEightPackedGapEightMask = 0) (i : Fin 16) :
    (8 : ℤ) ∣ generatedRootEightPackedSignedDigit w i := by
  have hp : 512 ^ i.val = 2 ^ (9 * i.val) := by rw [pow_mul]; norm_num
  have hz := generatedRootEight_packed_gap_mask_digit w generatedRootEightPackedGapEightMask
    9 3 i.val (by decide) (gap_eight_mask_digits i) hgap
  change (w / 2 ^ (9 * i.val) % 512) % 8 = 0 at hz
  rw [← hp] at hz
  have hd : (8 : ℤ) ∣ ((w / 512 ^ i.val % 512 : ℕ) : ℤ) := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero hz
  dsimp only [generatedRootEightPackedSignedDigit]
  split_ifs
  · exact hd
  · exact dvd_sub hd (by decide)

/-- A complete four-term word equation with original low-bit certificates implies all original Fourier equations. -/
theorem generatedRootEight_packed_signed_four_terms (w : Fin 4 → ℕ) (t : ℕ)
    (c : Fin 4 → ℤ) (hc : ∀ j, |c j| ≤ 1)
    (hw : ∀ j, w j < 512 ^ 16) (ht : t < 512 ^ 16)
    (hg : ∀ j, w j &&& generatedRootEightPackedGapEightMask = 0)
    (hgt : t &&& generatedRootEightPackedGapEightMask = 0)
    (he : (∑ j : Fin 4, c j * generatedRootEightPackedSignedWord (w j)) =
      2 * generatedRootEightPackedSignedWord t) :
    ∀ i : Fin 16, (∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i) =
      2 * generatedRootEightPackedSignedDigit t i := by
  apply generatedRootEight_packed_signed_linear w t c 2 8 (by norm_num) hw ht
  · intro i
    apply dvd_sub
    · apply Finset.dvd_sum
      intro j _
      exact dvd_mul_of_dvd_right (generatedRootEight_packed_signed_digit_eight _ (hg j) i) _
    · exact dvd_mul_of_dvd_right (generatedRootEight_packed_signed_digit_eight _ hgt i) _
  · intro i
    have hs : |∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i| ≤ 1024 := by
      calc
        _ ≤ ∑ j : Fin 4, |c j * generatedRootEightPackedSignedDigit (w j) i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 4, (256 : ℤ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have hd := generatedRootEight_packed_signed_digit_abs (w j) i
          have hj := hc j
          have hn := abs_nonneg (generatedRootEightPackedSignedDigit (w j) i)
          nlinarith [abs_nonneg (c j)]
        _ = 1024 := by norm_num
    have htbound := generatedRootEight_packed_signed_digit_abs t i
    have hb := abs_sub_le (∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i)
      0 (2 * generatedRootEightPackedSignedDigit t i)
    simp only [sub_zero, zero_sub, abs_neg] at hb
    rw [abs_mul] at hb
    norm_num at hb
    linarith
  · exact he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
