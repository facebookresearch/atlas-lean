/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateCPacket002Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateCPacket002Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateCPacket002Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateCPacket002Block03

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceBoundedQuantifier256

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateGeneric

/-! Ungated complete original final source certificates; no discovery premise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem source_block_00 :
    ∀ u : Fin 64, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCLabel 2 ⟨64 * 0 + u.val, by omega⟩) :=
  generatedTenth_final_source_C_002_block_00

private theorem source_block_01 :
    ∀ u : Fin 64, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCLabel 2 ⟨64 * 1 + u.val, by omega⟩) :=
  generatedTenth_final_source_C_002_block_01

private theorem source_block_02 :
    ∀ u : Fin 64, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCLabel 2 ⟨64 * 2 + u.val, by omega⟩) :=
  generatedTenth_final_source_C_002_block_02

private theorem source_block_03 :
    ∀ u : Fin 64, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCLabel 2 ⟨64 * 3 + u.val, by omega⟩) :=
  generatedTenth_final_source_C_002_block_03

set_option maxHeartbeats 8000000 in
-- Scope the complete original integer final-Xi source formula to this packet.
/-- Every original source address is checked, including zero coefficients. -/
theorem generatedTenth_final_source_certificate_C_002 :
    ∀ u : Fin 256, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCLabel 2 u) := by
  apply generatedTenth_final_source_predicate256_of_blocks
  intro b
  fin_cases b
  · exact source_block_00
  · exact source_block_01
  · exact source_block_02
  · exact source_block_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
