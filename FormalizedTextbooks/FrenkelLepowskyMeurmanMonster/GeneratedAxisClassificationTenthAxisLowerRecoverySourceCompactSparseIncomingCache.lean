/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactSparseIncomingActual

/-! Ungated complete paired sparse compact source formula; no finite cache proof is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every prospective incoming integer cache value must equal the full64-term source numerator. -/
def GeneratedTenthSourceCompactSparseIncomingCacheCertificate
    (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ k i, generatedTenthSourceCompactSparseIncomingQ k i = (B k i : ℚ)

/-- Full equality gives all 98,304 incoming coordinates at their physical scale. -/
theorem generatedTenth_source_compact_sparse_incoming_cache
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthSourceCompactSparseIncomingCacheCertificate B)
    (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (B k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_compact_sparse_incoming_actual hanchor k i, hB k i]
  norm_cast

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
