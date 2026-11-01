/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumActual

/-! Ungated incoming B word implication with residual divisibility4 and original scalar4. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete packed equations give all original spin-label and physical-column integer equations.
Only the weighted residual must be divisible by4; the target B need not have a gap certificate. -/
theorem generatedTenth_incoming_B_packed_integer
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hc : GeneratedTenthSourceColumnSpinSumCacheCertificate cache)
    (B : Fin 4096 → Fin 24 → ℤ) (hb : GeneratedTenthIncomingBPackedTargetBound B)
    (hw : GeneratedTenthIncomingBPackedWordCertificate cache B) :
    GeneratedTenthSourceColumnSpinSumBIntegerCertificate cache B := by
  intro k j
  let a : Fin 256 := ⟨k.val / 16, by omega⟩
  let s : Fin 16 := ⟨k.val % 16, Nat.mod_lt _ (by decide)⟩
  have he := generatedRootEight_packed_signed_linear
    (fun r : Fin 8 => generatedTenthIncomingBPackedSourceWord cache r a)
    (generatedTenthIncomingBPackedTargetWord B j a)
    (fun r => generatedTenthSourceSpatialWordLiteralNumerator j
      (generatedTwelfthTensorSourceCoordinate r)) 4 4 (by norm_num)
    (fun _ => generatedTenth_packed_boundary_word_lt _)
    (generatedTenth_packed_boundary_word_lt _)
    (fun i => by
      apply dvd_sub
      · apply Finset.dvd_sum
        intro r _
        rw [generatedTenth_incoming_B_packed_source_digit cache hc]
        exact dvd_mul_of_dvd_right
          (hc r (generatedNinthLowerSpinPackedPrefixIndex a i)).2.1 _
      · exact ⟨generatedRootEightPackedSignedDigit
          (generatedTenthIncomingBPackedTargetWord B j a) i, rfl⟩)
    (fun i => by
      have hs : |∑ r : Fin 8, generatedTenthSourceSpatialWordLiteralNumerator j
          (generatedTwelfthTensorSourceCoordinate r) *
            generatedRootEightPackedSignedDigit
              (generatedTenthIncomingBPackedSourceWord cache r a) i| ≤ 256 := by
        calc
          _ ≤ ∑ r : Fin 8, |generatedTenthSourceSpatialWordLiteralNumerator j
              (generatedTwelfthTensorSourceCoordinate r) *
                generatedRootEightPackedSignedDigit
                  (generatedTenthIncomingBPackedSourceWord cache r a) i| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _r : Fin 8, (32 : ℤ) := by
            apply Finset.sum_le_sum
            intro r _
            rw [abs_mul, generatedTenth_incoming_B_packed_source_digit cache hc]
            have hP := generatedTenth_incoming_B_packed_physical_bound j r
            have hS := (hc r (generatedNinthLowerSpinPackedPrefixIndex a i)).2.2
            nlinarith [abs_nonneg (generatedTenthSourceSpatialWordLiteralNumerator j
              (generatedTwelfthTensorSourceCoordinate r)),
              abs_nonneg (cache r (generatedNinthLowerSpinPackedPrefixIndex a i))]
          _ = _ := by norm_num
      have ht := generatedTenth_incoming_B_packed_target_abs B hb j a i
      rw [← generatedTenth_incoming_B_packed_target_digit B hb j a i] at ht
      have hx := abs_sub_le
        (∑ r : Fin 8, generatedTenthSourceSpatialWordLiteralNumerator j
          (generatedTwelfthTensorSourceCoordinate r) *
            generatedRootEightPackedSignedDigit
              (generatedTenthIncomingBPackedSourceWord cache r a) i) 0
        (4 * generatedRootEightPackedSignedDigit (generatedTenthIncomingBPackedTargetWord B j a) i)
      simp only [sub_zero, zero_sub, abs_neg] at hx
      rw [abs_mul] at hx
      norm_num at hx ⊢
      linarith)
    (hw j a)
  have hi := he s
  have hk : generatedNinthLowerSpinPackedPrefixIndex a s = k := by
    apply Fin.ext
    dsimp [generatedNinthLowerSpinPackedPrefixIndex, a, s]
    omega
  simp only [generatedTenth_incoming_B_packed_source_digit cache hc,
    generatedTenth_incoming_B_packed_target_digit B hb, hk] at hi
  exact hi.symm.trans (by
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _)

/-- Packed B calibration keeps the genuine full-Q, phase, P, and anchor conditions. -/
theorem generatedTenth_incoming_B_packed_calibration
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate generatedTenthSourceSpatialWordLiteral)
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hc : GeneratedTenthSourceColumnSpinSumCacheCertificate cache)
    (B : Fin 4096 → Fin 24 → ℤ) (hb : GeneratedTenthIncomingBPackedTargetBound B)
    (hw : GeneratedTenthIncomingBPackedWordCertificate cache B) :
    GeneratedTenthFinalShortSourceTensorCalibration B := by
  apply generatedTenth_source_column_spin_sum_B_calibration hanchor hQ hzero hP cache
    (fun r k => (hc r k).1) B
  exact generatedTenth_incoming_B_packed_integer cache hc B hb hw

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
