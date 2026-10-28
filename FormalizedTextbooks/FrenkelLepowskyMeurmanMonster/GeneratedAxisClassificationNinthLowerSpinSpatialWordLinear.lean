/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedFourier

/-! Complete four-source signed-word implications for exact sparse spatial replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- Both low bits of every original signed nine-bit slot. -/
def generatedNinthLowerSpinSpatialGapFourMask : ℕ :=
  130924140108790351124475841131007993185795

private theorem gap_four_mask_digits : ∀ i : Fin 16,
    generatedNinthLowerSpinSpatialGapFourMask / 2 ^ (9 * i.val) % 2 ^ 2 = 3 := by
  decide +kernel

/-- A whole-word low-bit certificate gives divisibility of every original signed slot. -/
theorem generatedNinth_lower_spin_spatial_signed_digit_four (w : ℕ)
    (hgap : w &&& generatedNinthLowerSpinSpatialGapFourMask = 0) (i : Fin 16) :
    (4 : ℤ) ∣ generatedRootEightPackedSignedDigit w i := by
  have hp : 512 ^ i.val = 2 ^ (9 * i.val) := by rw [pow_mul]; norm_num
  have hz := generatedRootEight_packed_gap_mask_digit w
    generatedNinthLowerSpinSpatialGapFourMask 9 2 i.val (by decide)
    (gap_four_mask_digits i) hgap
  change (w / 2 ^ (9 * i.val) % 512) % 4 = 0 at hz
  rw [← hp] at hz
  have hd : (4 : ℤ) ∣ ((w / 512 ^ i.val % 512 : ℕ) : ℤ) := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero hz
  dsimp only [generatedRootEightPackedSignedDigit]
  split_ifs
  · exact hd
  · exact dvd_sub hd (by decide)

/-- One exact four-source word equation implies all sixteen original spatial equations. -/
theorem generatedNinth_lower_spin_spatial_four_signed_words
    (w : Fin 4 → ℕ) (t : ℕ) (c : Fin 4 → ℤ) (B G : ℤ)
    (hB : 0 ≤ B) (hG : 0 < G) (hbound : 4 * B + 256 < G * 512)
    (hc : ∀ j, |c j| ≤ 1)
    (hw : ∀ j, w j < 512 ^ 16) (ht : t < 512 ^ 16)
    (hb : ∀ j i, |generatedRootEightPackedSignedDigit (w j) i| ≤ B)
    (hg : ∀ j i, G ∣ generatedRootEightPackedSignedDigit (w j) i)
    (hgt : ∀ i, G ∣ generatedRootEightPackedSignedDigit t i)
    (he : (∑ j : Fin 4, c j * generatedRootEightPackedSignedWord (w j)) =
      generatedRootEightPackedSignedWord t) :
    ∀ i : Fin 16, (∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i) =
      generatedRootEightPackedSignedDigit t i := by
  suffices h : ∀ i : Fin 16,
      (∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i) =
        1 * generatedRootEightPackedSignedDigit t i by
    simpa only [one_mul] using h
  apply generatedRootEight_packed_signed_linear w t c 1 G hG hw ht
  · intro i
    apply dvd_sub
    · apply Finset.dvd_sum
      intro j _
      exact dvd_mul_of_dvd_right (hg j i) _
    · simpa only [one_mul] using hgt i
  · intro i
    simp only [one_mul]
    have hs : |∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i| ≤
        4 * B := by
      calc
        _ ≤ ∑ j : Fin 4, |c j * generatedRootEightPackedSignedDigit (w j) i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 4, B := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have hd := hb j i
          have hj := hc j
          have hn := abs_nonneg (generatedRootEightPackedSignedDigit (w j) i)
          nlinarith [abs_nonneg (c j)]
        _ = 4 * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
    have htbound := generatedRootEight_packed_signed_digit_abs t i
    have habs := abs_sub_le (∑ j : Fin 4, c j * generatedRootEightPackedSignedDigit (w j) i)
      0 (1 * generatedRootEightPackedSignedDigit t i)
    simp only [sub_zero, zero_sub, abs_neg, one_mul] at habs
    linarith
  · simpa only [one_mul] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
