/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactSparseIncomingFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactIncomingTensor

/-! Ungated complete paired sparse compact source formula; no finite cache proof is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- One genuine paired atom retains both delta signs, all compact central phases, and its full
original spatial source column. -/
theorem generatedTenth_source_compact_sparse_atom_actual
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (k : Fin 4096) (i : Fin 24) :
    generatedTenthAxisLowerRecoverySourceCompactTensor
      (generatedTenthSourceInitialTensorSparseAtom p) (golayLabelCoefficients k) i =
      (generatedTenthSourceInitialTensorSparseSign p : ℝ) *
        ((generatedTenthSourceCompactSparseIncomingLowSign p (golayLabelCoefficients k) : ℝ) -
          (generatedTenthSourceCompactSparseIncomingHighSign p (golayLabelCoefficients k) : ℝ)) *
            (generatedAxisGlobalFifthSpatialWordMatrix 2 i
              (generatedTenthSourceInitialTensorSparseCoordinate p) : ℝ) /
                (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_compact_sparse_initial_atom, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [generatedTenth_source_delta_compact_tensor_factors]
  simp only [map_sub, Pi.sub_apply]
  rw [generatedTenth_source_compact_delta_phase, generatedTenth_source_compact_delta_phase,
    generatedTenth_source_compact_sparse_spatial_column]
  simp only [generatedTenthSourceCompactSparseIncomingLowSign,
    generatedTenthSourceCompactSparseIncomingHighSign, generatedAxisGlobalIntSign_real]
  ring

/-- The actual complete incoming Root02 tensor follows from64 paired compact source terms,
under the genuine combined anchor; there is no original seven-stage coordinate replay. -/
theorem generatedTenth_source_compact_sparse_incoming_actual
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceCompactSparseIncomingQ k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_compact_incoming_tensor hanchor,
    generatedTenth_source_initial_tensor_sparse_actual_sum, map_sum]
  simp only [Finset.sum_apply]
  simp_rw [generatedTenth_source_compact_sparse_atom_actual]
  unfold generatedTenthSourceCompactSparseIncomingQ
  push_cast
  rw [Finset.sum_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
