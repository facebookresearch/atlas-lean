/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactSparseIncomingCache

/-! Ungated exact128-image rational source evaluator, preserving all64 paired incoming terms.
P is the physical spatial word, distinct from the incoming axis matrix block M. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A literal P requires the complete576-entry original physical word equality. -/
def GeneratedTenthSourceSparseFastSpatialCertificate
    (P : Matrix (Fin 24) (Fin 24) ℚ) : Prop :=
  ∀ i j, P i j = generatedAxisGlobalFifthSpatialWordMatrix 2 i j

/-- The entire original rational source numerator uses cached full-Q images and exact phase. -/
def generatedTenthSourceSparseFastIncomingQ
    (P : Matrix (Fin 24) (Fin 24) ℚ) (k : Fin 4096) (i : Fin 24) : ℚ :=
  ∑ p : GeneratedTenthSourceInitialTensorSparseIndex,
    (generatedTenthSourceInitialTensorSparseSign p : ℚ) *
      ((generatedTenthSourceSparseFastSign p 0 (golayLabelCoefficients k) : ℚ) -
        (generatedTenthSourceSparseFastSign p 1 (golayLabelCoefficients k) : ℚ)) *
          P i (generatedTenthSourceInitialTensorSparseCoordinate p)

/-- All physical word entries remain the actual original spatial operator's coordinates. -/
theorem generatedTenth_source_sparse_fast_spatial_actual
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P) (i j : Fin 24) :
    leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 2) i j = (P i j : ℝ) := by
  rw [hP i j, generatedAxisGlobalFifthSpatialWordMatrix_coordinate]
  rfl

/-- Every fast rational value equals the complete genuine original paired source formula. -/
theorem generatedTenth_source_sparse_fast_incoming_eq
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P) (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceSparseFastIncomingQ P k i =
      generatedTenthSourceCompactSparseIncomingQ k i := by
  unfold generatedTenthSourceSparseFastIncomingQ generatedTenthSourceCompactSparseIncomingQ
  apply Finset.sum_congr rfl
  intro p _
  rw [generatedTenth_source_sparse_fast_low_sign hQ,
    generatedTenth_source_sparse_fast_high_sign hQ, hP]

/-- The genuine combined tensor anchor, not a binary-only orientation, binds the entire source. -/
theorem generatedTenth_source_sparse_fast_incoming_actual
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (P : Matrix (Fin 24) (Fin 24) ℚ)
    (hP : GeneratedTenthSourceSparseFastSpatialCertificate P) (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceSparseFastIncomingQ P k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_sparse_fast_incoming_eq hQ P hP]
  exact generatedTenth_source_compact_sparse_incoming_actual hanchor k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

