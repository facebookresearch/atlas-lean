/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumAll

/-! Ungated genuine8-column tensor source and exact weighted B equality interface.
Full-Q, delta0 phase, physical P, and the genuine combined anchor remain explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete actual tensor is the eight cached spin sums times the original physical columns. -/
theorem generatedTenth_source_column_spin_sum_incoming_actual
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hcache : GeneratedTenthSourceColumnSpinSumSourceCertificate cache)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P) (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceColumnSpinSumIncomingQ cache P k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_column_spin_sum_incoming_eq cache hcache P k i]
  exact generatedTenth_source_delta_zero_cached_incoming_actual hanchor hQ hzero P hP k i

/-- Complete weighted integer B equality uses the full literal P numerator at denominator4. -/
def GeneratedTenthSourceColumnSpinSumBIntegerCertificate
    (cache : Fin 8 → Fin 4096 → ℤ) (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ k i, 4 * B k i =
    ∑ r : Fin 8, cache r k * generatedTenthSourceSpatialWordLiteralNumerator i
      (generatedTwelfthTensorSourceCoordinate r)

/-- The entire weighted integer certificate implies complete rational source-cache equality. -/
theorem generatedTenth_source_column_spin_sum_B_rational
    (cache : Fin 8 → Fin 4096 → ℤ) (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate cache B)
    (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceColumnSpinSumIncomingQ cache generatedTenthSourceSpatialWordLiteral k i =
      (B k i : ℚ) := by
  unfold generatedTenthSourceColumnSpinSumIncomingQ generatedTenthSourceSpatialWordLiteral
    generatedTenthSourceSpatialWordLiteralDenominator
  calc
    _ = ((∑ r : Fin 8, cache r k * generatedTenthSourceSpatialWordLiteralNumerator i
        (generatedTwelfthTensorSourceCoordinate r) : ℤ) : ℚ) / 4 := by
      simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [← hB k i]
      push_cast
      ring

/-- All98304 complete integer equalities give the prior full B source certificate. -/
theorem generatedTenth_source_column_spin_sum_B_certificate
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hcache : GeneratedTenthSourceColumnSpinSumSourceCertificate cache)
    (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate cache B) :
    GeneratedTenthSourceDeltaZeroCachedBCertificate generatedTenthSourceSpatialWordLiteral B := by
  intro k i
  rw [← generatedTenth_source_column_spin_sum_incoming_eq cache hcache]
  exact generatedTenth_source_column_spin_sum_B_rational cache B hB k i

/-- Genuine B/64 calibration follows with all source phases, P, and the combined anchor explicit. -/
theorem generatedTenth_source_column_spin_sum_B_calibration
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate generatedTenthSourceSpatialWordLiteral)
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hcache : GeneratedTenthSourceColumnSpinSumSourceCertificate cache)
    (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate cache B) :
    GeneratedTenthFinalShortSourceTensorCalibration B :=
  generatedTenth_source_delta_zero_cached_B_calibration hanchor hQ hzero
    generatedTenthSourceSpatialWordLiteral hP B
    (generatedTenth_source_column_spin_sum_B_certificate cache hcache B hB)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

