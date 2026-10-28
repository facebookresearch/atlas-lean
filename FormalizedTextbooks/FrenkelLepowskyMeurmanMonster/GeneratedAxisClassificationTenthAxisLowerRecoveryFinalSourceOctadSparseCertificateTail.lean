/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceOctadSparseCertificatesGeneric

/-! Closed exact incoming-source tail; this draft requires the genuine standard gates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
-- Reduce the complete closed balanced source dictionaries on the exact source tail only.
set_option maxHeartbeats 8000000 in
-- Check all 192 original tail coefficients, including every retained zero.
/-- The exact source tail covers original octads 756, 757, and 758 without padding. -/
theorem generatedTenth_final_source_octad_sparse_source_tail :
    ∀ u : Fin 192, GeneratedTenthFinalSourceOctadSparseCertificate
      (generatedTenthFinalSourceOctadSparseTailAddress u) := by
  unfold GeneratedTenthFinalSourceOctadSparseCertificate
    generatedTenthFinalSourceOctadSparseTailAddress
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
