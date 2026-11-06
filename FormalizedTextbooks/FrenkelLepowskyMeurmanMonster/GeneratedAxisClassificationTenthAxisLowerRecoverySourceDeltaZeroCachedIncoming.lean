/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaZeroSignCacheAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastIncomingCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordLiteralData

/-! Ungated64-paired-term source evaluator:128 full Pauli images and a whole4096 delta0 sign cache.
The repeated postquadratic and inverse-left calculation becomes a checked sign lookup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Original full image central/modulation phase times the cached shifted delta0 sign. -/
def generatedTenthSourceDeltaZeroCachedSign
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) (t : SpinIndex) : ℤ :=
  let q := generatedTenthSourceSparseFastQ p b
  generatedAxisGlobalIntSign (spinPhase q t) *
    generatedTenthSourceDeltaZeroSignCache (generatedAxisGlobalSpinLabel (t + spinTranslation q))

/-- Complete cached signs equal the earlier full-phase evaluator; no spin orientation is chosen. -/
theorem generatedTenth_source_delta_zero_cached_sign_eq
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) (t : SpinIndex) :
    generatedTenthSourceDeltaZeroCachedSign p b t =
      generatedTenthSourceSparseFastSign p b t := by
  unfold generatedTenthSourceDeltaZeroCachedSign generatedTenthSourceSparseFastSign
    generatedTenthSourceSparseFastDeltaPhase
  dsimp only
  rw [generatedTenth_source_delta_zero_sign_cache_spin hzero]
  exact (generatedTwelfth_tensor_source_int_sign_add _ _).symm

/-- Complete rational numerator, with all64 original paired terms and every physical column. -/
def generatedTenthSourceDeltaZeroCachedIncomingQ
    (P : Matrix (Fin 24) (Fin 24) ℚ) (k : Fin 4096) (i : Fin 24) : ℚ :=
  ∑ p : GeneratedTenthSourceInitialTensorSparseIndex,
    (generatedTenthSourceInitialTensorSparseSign p : ℚ) *
      ((generatedTenthSourceDeltaZeroCachedSign p 0 (golayLabelCoefficients k) : ℚ) -
        (generatedTenthSourceDeltaZeroCachedSign p 1 (golayLabelCoefficients k) : ℚ)) *
          P i (generatedTenthSourceInitialTensorSparseCoordinate p)

/-- The literal P specialization retains its separate full576-entry source certificate. -/
def generatedTenthSourceDeltaZeroCachedLiteralQ (k : Fin 4096) (i : Fin 24) : ℚ :=
  generatedTenthSourceDeltaZeroCachedIncomingQ generatedTenthSourceSpatialWordLiteral k i

/-- Every cached rational value equals the prior complete genuine source expression. -/
theorem generatedTenth_source_delta_zero_cached_incoming_eq
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ) (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceDeltaZeroCachedIncomingQ P k i =
      generatedTenthSourceSparseFastIncomingQ P k i := by
  unfold generatedTenthSourceDeltaZeroCachedIncomingQ generatedTenthSourceSparseFastIncomingQ
  simp_rw [generatedTenth_source_delta_zero_cached_sign_eq hzero]

/-- Genuine combined anchor, full128 Q images, and full physical P still bind all actual entries. -/
theorem generatedTenth_source_delta_zero_cached_incoming_actual
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P) (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceDeltaZeroCachedIncomingQ P k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_delta_zero_cached_incoming_eq hzero]
  exact generatedTenth_source_sparse_fast_incoming_actual hanchor hQ P hP k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

