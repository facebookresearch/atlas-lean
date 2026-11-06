/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastIncomingFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceCalibration

/-! Ungated practical B-source bridge. Complete98304 rational-to-integer equality stays explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every incoming B entry must equal the entire rational64-paired-term fast source expression. -/
def GeneratedTenthSourceSparseFastIncomingCacheCertificate
    (P : Matrix (Fin 24) (Fin 24) ℚ) (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ k i, generatedTenthSourceSparseFastIncomingQ P k i = (B k i : ℚ)

/-- Exact fast-cache equality also certifies the earlier complete genuine sparse expression. -/
theorem generatedTenth_source_sparse_fast_cache_original
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P)
    (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceSparseFastIncomingCacheCertificate P B) :
    GeneratedTenthSourceCompactSparseIncomingCacheCertificate B := by
  intro k i
  rw [← generatedTenth_source_sparse_fast_incoming_eq hQ P hP, hB k i]

/-- Genuine combined-anchor binding and the complete finite B equality give every actual entry. -/
theorem generatedTenth_source_sparse_fast_incoming_cache
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P)
    (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceSparseFastIncomingCacheCertificate P B)
    (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (B k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_sparse_fast_incoming_actual hanchor hQ P hP k i, hB k i]
  norm_cast

/-- Actual incoming equality calibrates B/64 against the already proved eight-factor source. -/
theorem generatedTenth_source_sparse_fast_B_calibration
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P)
    (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceSparseFastIncomingCacheCertificate P B) :
    GeneratedTenthFinalShortSourceTensorCalibration B := by
  intro k i
  have h := (generatedTenth_final_short_source_tensor_actual k i).symm.trans
    (generatedTenth_source_sparse_fast_incoming_cache hanchor hQ P hP B hB k i)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have he : (generatedTenthFinalShortSourceTensorQ k i : ℝ) = (B k i : ℝ) / 64 := by
    field_simp [hs] at h
    nlinarith [h]
  exact_mod_cast he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

