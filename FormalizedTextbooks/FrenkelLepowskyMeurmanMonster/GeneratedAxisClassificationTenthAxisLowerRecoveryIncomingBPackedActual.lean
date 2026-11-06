/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingTensorPackedCache

/-! Ungated original incoming B cache binding. Every zero and original24*k+i lookup is retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The finite B bound always concerns the complete original sparse lookup, including its zeros. -/
def GeneratedTenthIncomingBPackedActualBound : Prop :=
  GeneratedTenthIncomingBPackedTargetBound generatedTenthIncomingTensorPackedCache

/-- The complete finite word certificate uses all Sj caches and original incoming B values. -/
def GeneratedTenthIncomingBPackedActualWords : Prop :=
  GeneratedTenthIncomingBPackedWordCertificate generatedTenthSourceColumnSpinSumCache
    generatedTenthIncomingTensorPackedCache

/-- The original interleaved spin/physical address is retained exactly. -/
theorem generatedTenth_incoming_B_packed_original_address (k : Fin 4096) (j : Fin 24) :
    generatedTenthIncomingTensorPackedCache k j =
      generatedTenthIncomingTensorPackedCacheAddressValue ⟨24 * k.val + j.val, by omega⟩ := by
  rfl

/-- Every packed target slot binds its original exact source address, including zero values. -/
theorem generatedTenth_incoming_B_packed_actual_target_digit
    (hb : GeneratedTenthIncomingBPackedActualBound) (j : Fin 24) (a : Fin 256) (s : Fin 16) :
    generatedRootEightPackedSignedDigit
      (generatedTenthIncomingBPackedTargetWord generatedTenthIncomingTensorPackedCache j a) s =
        generatedTenthIncomingTensorPackedCacheAddressValue
          ⟨24 * (generatedNinthLowerSpinPackedPrefixIndex a s).val + j.val, by omega⟩ := by
  rw [generatedTenth_incoming_B_packed_target_digit generatedTenthIncomingTensorPackedCache hb]
  rfl

/-- Every source word slot is its complete original eight-pair spin sum, with all full phases. -/
theorem generatedTenth_incoming_B_packed_actual_source_digit
    (r : Fin 8) (a : Fin 256) (s : Fin 16) :
    generatedRootEightPackedSignedDigit
      (generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache r a) s =
        generatedTenthSourceColumnSpinSum r (generatedNinthLowerSpinPackedPrefixIndex a s) := by
  rw [generatedTenth_incoming_B_packed_source_digit generatedTenthSourceColumnSpinSumCache
    generatedTenth_source_column_spin_sum_cache_certificate]
  exact generatedTenth_source_column_spin_sum_source_certificate r _

/-- All98304 weighted integer B equations follow from6144 complete finite word equations. -/
theorem generatedTenth_incoming_B_packed_actual_integer
    (hb : GeneratedTenthIncomingBPackedActualBound)
    (hw : GeneratedTenthIncomingBPackedActualWords) :
    GeneratedTenthSourceColumnSpinSumBIntegerCertificate generatedTenthSourceColumnSpinSumCache
      generatedTenthIncomingTensorPackedCache :=
  generatedTenth_incoming_B_packed_integer generatedTenthSourceColumnSpinSumCache
    generatedTenth_source_column_spin_sum_cache_certificate generatedTenthIncomingTensorPackedCache
    hb hw

/-- The actual incoming B tensor calibration retains all genuine original source obligations. -/
theorem generatedTenth_incoming_B_packed_actual_calibration
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate generatedTenthSourceSpatialWordLiteral)
    (hb : GeneratedTenthIncomingBPackedActualBound)
    (hw : GeneratedTenthIncomingBPackedActualWords) :
    GeneratedTenthFinalShortSourceTensorCalibration generatedTenthIncomingTensorPackedCache :=
  generatedTenth_incoming_B_packed_calibration hanchor hQ hzero hP
    generatedTenthSourceColumnSpinSumCache generatedTenth_source_column_spin_sum_cache_certificate
    generatedTenthIncomingTensorPackedCache hb hw

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
