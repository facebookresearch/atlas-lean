/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceIncomingMatrixLiteralData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordLiteralCertificate

/-! Ungated complete literal original Root02 rational matrix source cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem source_physical_word_literal :
    generatedAxisGlobalFifthSpatialWordMatrix 2 = generatedTenthSourceSpatialWordLiteral := by
  funext i j
  exact (generatedTenth_source_spatial_word_literal_certificate i j).symm

set_option maxHeartbeats 8000000 in
-- Check all 576 M coordinates after the frozen full physical P equality rewrite.
/-- Every literal rational cache entry equals the original seven-stage matrix source expression. -/
theorem generatedTenth_source_incoming_matrix_literal_certificate :
    ∀ i j : Fin 24,
      generatedTenthSourceIncomingMatrixLiteral i j = generatedTenthSourceIncomingMatrix i j := by
  unfold generatedTenthSourceIncomingMatrix generatedAxisGlobalFifthRootMatrixQ
  rw [source_physical_word_literal]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
