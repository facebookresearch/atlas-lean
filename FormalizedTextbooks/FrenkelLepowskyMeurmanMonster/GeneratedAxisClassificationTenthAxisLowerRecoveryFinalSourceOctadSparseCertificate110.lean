/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceOctadSparseCertificatesGeneric

/-! Closed exact incoming-source packet; this draft requires the genuine standard gates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
-- Reduce the complete closed balanced source dictionaries on this packet only.
set_option maxHeartbeats 8000000 in
-- Check 256 original incoming coefficients, retaining every zero and signed source slot.
/-- Complete original incoming source packet 110, before any triality output computation. -/
theorem generatedTenth_final_source_octad_sparse_source_110 :
    ∀ u : Fin 256, GeneratedTenthFinalSourceOctadSparseCertificate
      (generatedTenthFinalSourceOctadSparsePacketAddress ⟨110, by omega⟩ u) := by
  unfold GeneratedTenthFinalSourceOctadSparseCertificate
    generatedTenthFinalSourceOctadSparsePacketAddress
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
