/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateGeneric

/-! Ungated exact candidate support data/certificates; numerical parsing is not proof. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Scope exact support coverage to this original finite address block.
/-- Every nonzero source in the complete address block is retained, including defaults. -/
theorem generatedTenth_two_fixer_c_support_coverage_22 :
    ∀ u : Fin 1024, GeneratedTenthTwoFixerCSupportCoverage
      (generatedTenthTwoFixerCSupportCoverageLabel 22 u) := by
  unfold GeneratedTenthTwoFixerCSupportCoverage
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
