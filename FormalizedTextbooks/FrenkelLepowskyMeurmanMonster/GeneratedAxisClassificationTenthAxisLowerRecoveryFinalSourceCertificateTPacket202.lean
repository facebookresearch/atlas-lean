/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateGeneric

/-! Ungated complete original final source certificates; no discovery premise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Scope the complete original integer final-Xi source formula to this packet.
/-- Every original source address is checked, including zero coefficients. -/
theorem generatedTenth_final_source_certificate_T_202 :
    ∀ u : Fin 256, GeneratedTenthFinalSourceCertificateT
      (generatedTenthFinalSourceCertificateTLabel 202 u) := by
  unfold GeneratedTenthFinalSourceCertificateT
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
