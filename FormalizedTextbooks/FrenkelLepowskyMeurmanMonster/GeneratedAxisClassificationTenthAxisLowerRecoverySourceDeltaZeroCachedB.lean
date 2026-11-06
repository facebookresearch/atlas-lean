/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaZeroCachedIncoming

/-! Ungated complete B-cache certificate interface. No98304-value finite expansion is made. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every B entry must equal the entire normalized64-paired-term rational source numerator. -/
def GeneratedTenthSourceDeltaZeroCachedBCertificate
    (P : Matrix (Fin 24) (Fin 24) ℚ) (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ k i, generatedTenthSourceDeltaZeroCachedIncomingQ P k i = (B k i : ℚ)

/-- Whole B equality also certifies the earlier exact fast formula. -/
theorem generatedTenth_source_delta_zero_cached_B_original
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (B : Fin 4096 → Fin 24 → ℤ) (hB : GeneratedTenthSourceDeltaZeroCachedBCertificate P B) :
    GeneratedTenthSourceSparseFastIncomingCacheCertificate P B := by
  intro k i
  rw [← generatedTenth_source_delta_zero_cached_incoming_eq hzero, hB k i]

/-- The actual complete incoming tensor follows only after all source and B certificates. -/
theorem generatedTenth_source_delta_zero_cached_B_actual
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P)
    (B : Fin 4096 → Fin 24 → ℤ) (hB : GeneratedTenthSourceDeltaZeroCachedBCertificate P B)
    (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (B k i : ℝ) / (64 * Real.sqrt 2) := by
  exact generatedTenth_source_sparse_fast_incoming_cache hanchor hQ P hP B
    (generatedTenth_source_delta_zero_cached_B_original hzero P B hB) k i

/-- The exact B/64 calibration remains the genuine eight-factor incoming tensor source. -/
theorem generatedTenth_source_delta_zero_cached_B_calibration
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P)
    (B : Fin 4096 → Fin 24 → ℤ) (hB : GeneratedTenthSourceDeltaZeroCachedBCertificate P B) :
    GeneratedTenthFinalShortSourceTensorCalibration B :=
  generatedTenth_source_sparse_fast_B_calibration hanchor hQ P hP B
    (generatedTenth_source_delta_zero_cached_B_original hzero P B hB)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

