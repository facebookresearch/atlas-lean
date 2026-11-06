/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalBActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastQCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaZeroSignCacheAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordLiteralCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorPhysicalActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorPackedPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! Conditional assembly of the original Tenth local count from the seven remaining complete
finite certificate families: the final C and T source caches, the incoming B integer equations,
the C support permutations of both genuine fibers, and the tensor boundary bounds and words.
Every premise is a finite certificate predicate about original source data, never a fixation,
stabilizer or orbit premise. These implications are infrastructure, not the closed count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete incoming B integer certificate gives the whole canonical incoming calibration. -/
theorem generatedTenth_finite_certificates_canonical_B
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate
      generatedTenthSourceColumnSpinSumCache generatedTenthIncomingTensorPackedCache) :
    GeneratedTenthSourceCompactCanonicalBCondition :=
  generatedTenth_source_compact_canonical_B_of_certificates
    generatedTenth_source_sparse_fast_q_certificate
    generatedTenth_source_delta_zero_sign_cache_certificate
    generatedTenth_source_spatial_word_literal_certificate
    generatedTenthSourceColumnSpinSumCache
    generatedTenth_source_column_spin_sum_source_certificate hB

/-- The seven finite certificate families make both genuine fibers fix the whole canonical axis. -/
theorem generatedTenth_finite_certificates_two_fixers
    (hC : ∀ a, GeneratedTenthFinalSourceCertificateC a)
    (hT : ∀ a, GeneratedTenthFinalSourceCertificateT a)
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate
      generatedTenthSourceColumnSpinSumCache generatedTenthIncomingTensorPackedCache)
    (hsupport : ∀ g, GeneratedTenthTwoFixerCSupportCondition g
      (generatedTenthTwoFixerCSupportDestination g) (generatedTenthTwoFixerCSupportPhase g))
    (hbounds : GeneratedTenthPackedBoundaryBounds)
    (hstart : GeneratedTenthPackedBoundaryStartWords)
    (hfinish : GeneratedTenthPackedBoundaryFinishWords) (g : Fin 2) :
    rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis := by
  have hcal := generatedTenth_finite_certificates_canonical_B hB
  exact generatedTenth_source_compact_canonical_two_fixers
    generatedTenthTwoFixerCSupportDestination generatedTenthTwoFixerCSupportPhase
    (generatedTenth_source_compact_canonical_C_input
      generatedTenth_root_two_certificates_all hcal hC)
    (generatedTenth_source_compact_canonical_T_input
      generatedTenth_root_two_certificates_all hcal hT)
    hsupport generatedTenth_two_fixer_tensor_physical_actual
    (generatedTenth_packed_boundary_start_actual hbounds hstart)
    generatedTenth_two_fixer_tensor_packed_pairs
    (generatedTenth_packed_boundary_finish_actual hbounds hfinish) g

/-- The original Tenth full-axis stabilizer order follows from the seven finite families. -/
theorem generatedTenth_local_axis_stabilizer_card_of_finite_certificates
    (hC : ∀ a, GeneratedTenthFinalSourceCertificateC a)
    (hT : ∀ a, GeneratedTenthFinalSourceCertificateT a)
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate
      generatedTenthSourceColumnSpinSumCache generatedTenthIncomingTensorPackedCache)
    (hsupport : ∀ g, GeneratedTenthTwoFixerCSupportCondition g
      (generatedTenthTwoFixerCSupportDestination g) (generatedTenthTwoFixerCSupportPhase g))
    (hbounds : GeneratedTenthPackedBoundaryBounds)
    (hstart : GeneratedTenthPackedBoundaryStartWords)
    (hfinish : GeneratedTenthPackedBoundaryFinishWords) :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 :=
  generatedTenth_source_compact_canonical_original_card
    (generatedTenth_finite_certificates_two_fixers hC hT hB hsupport hbounds hstart hfinish)

/-- Orbit-stabilizer turns the exact original stabilizer order into the exact local orbit size. -/
theorem generatedTenth_local_axis_orbit_card_of_stabilizer_card
    (hcard : Nat.card generatedTenthLocalAxisStabilizer = 2903040) :
    Nat.card (MulAction.orbit H generatedTenthAxis) = 48057153579122688000 := by
  have h := generatedTenthLocalAxisStabilizer.card_mul_index
  rw [hcard, local_h_card_exact] at h
  have hi : generatedTenthLocalAxisStabilizer.index = 48057153579122688000 := by omega
  rw [generatedTenthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
