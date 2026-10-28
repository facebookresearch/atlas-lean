/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedFourier

/-! Exact signed whole-word implications allowing coordinate sign masks. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- Up to thirteen signed whole words imply every original coordinate equation from exact low-bit certificates. -/
theorem generatedRootEight_packed_signed_bounded_terms {k : ℕ} (hk : k ≤ 13) (w : Fin k → ℕ) (t : ℕ)
    (c : Fin k → ℤ) (hc : ∀ j, |c j| ≤ 1)
    (hw : ∀ j, w j < 512 ^ 16) (ht : t < 512 ^ 16)
    (hg : ∀ j, w j &&& generatedRootEightPackedGapEightMask = 0)
    (hgt : t &&& generatedRootEightPackedGapEightMask = 0)
    (he : (∑ j : Fin k, c j * generatedRootEightPackedSignedWord (w j)) =
      2 * generatedRootEightPackedSignedWord t) :
    ∀ i : Fin 16, (∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i) =
      2 * generatedRootEightPackedSignedDigit t i := by
  apply generatedRootEight_packed_signed_linear w t c 2 8 (by norm_num) hw ht
  · intro i
    apply dvd_sub
    · apply Finset.dvd_sum
      intro j _
      exact dvd_mul_of_dvd_right (generatedRootEight_packed_signed_digit_eight _ (hg j) i) _
    · exact dvd_mul_of_dvd_right (generatedRootEight_packed_signed_digit_eight _ hgt i) _
  · intro i
    have hs : |∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i| ≤ (k : ℤ) * 256 := by
      calc
        _ ≤ ∑ j : Fin k, |c j * generatedRootEightPackedSignedDigit (w j) i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin k, (256 : ℤ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have hd := generatedRootEight_packed_signed_digit_abs (w j) i
          have hj := hc j
          have hn := abs_nonneg (generatedRootEightPackedSignedDigit (w j) i)
          nlinarith [abs_nonneg (c j)]
        _ = (k : ℤ) * 256 := by simp
    have htbound := generatedRootEight_packed_signed_digit_abs t i
    have hb := abs_sub_le (∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i)
      0 (2 * generatedRootEightPackedSignedDigit t i)
    simp only [sub_zero, zero_sub, abs_neg] at hb
    rw [abs_mul] at hb
    norm_num at hb
    have hkc : (k : ℤ) ≤ 13 := by exact_mod_cast hk
    nlinarith
  · exact he


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
