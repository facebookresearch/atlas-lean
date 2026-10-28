/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactIncomingAtoms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalFinalSourceActual

/-! Complete compact-source tensor calibration from genuine paired atoms and exact caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- Every actual compact incoming coordinate is the complete signed paired source formula. -/
theorem generatedTenth_source_compact_canonical_sparse_actual (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceCompactIncomingPacket.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceCompactSparseIncomingQ k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_compact_incoming_paired_atoms]
  simp only [Finset.sum_apply]
  simp_rw [generatedTenth_source_compact_sparse_atom_actual]
  unfold generatedTenthSourceCompactSparseIncomingQ
  push_cast
  rw [Finset.sum_div]

/-- The complete full-Q and delta-zero caches bind every compact incoming spin sum. -/
theorem generatedTenth_source_compact_canonical_column_actual
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hcache : GeneratedTenthSourceColumnSpinSumSourceCertificate cache)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P) (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceCompactIncomingPacket.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceColumnSpinSumIncomingQ cache P k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_column_spin_sum_incoming_eq cache hcache,
    generatedTenth_source_delta_zero_cached_incoming_eq hzero,
    generatedTenth_source_sparse_fast_incoming_eq hQ P hP]
  exact generatedTenth_source_compact_canonical_sparse_actual k i

/-- Exact whole weighted B equality calibrates the genuine canonical tensor without an anchor
hypothesis or a choice of the original source spin's scalar sign. -/
theorem generatedTenth_source_compact_canonical_B_of_certificates
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (hzero : GeneratedTenthSourceDeltaZeroSignCacheCertificate)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate generatedTenthSourceSpatialWordLiteral)
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hcache : GeneratedTenthSourceColumnSpinSumSourceCertificate cache)
    (hB : GeneratedTenthSourceColumnSpinSumBIntegerCertificate cache
      generatedTenthIncomingTensorPackedCache) :
    GeneratedTenthSourceCompactCanonicalBCondition := by
  intro k i
  rw [generatedTenth_source_compact_canonical_column_actual hQ hzero cache hcache _ hP,
    generatedTenth_source_column_spin_sum_B_rational cache _ hB]
  norm_cast

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
