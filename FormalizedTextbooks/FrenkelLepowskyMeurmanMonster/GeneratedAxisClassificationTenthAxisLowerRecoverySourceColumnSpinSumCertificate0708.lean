/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourcePauliCachedSign

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumData07

/-! Ungated exact original source column spin-sum candidate cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Scope the prospective closed256-label original eight-paired-term integer computation.
/-- Complete source equality for this column and every label of this original block. -/
theorem generatedTenth_source_column_spin_sum_certificate_07_08 :
    GeneratedTenthSourceColumnSpinSumBlockCertificate 7
      generatedTenthSourceColumnSpinSumCache07 8 := by
  unfold GeneratedTenthSourceColumnSpinSumBlockCertificate
  dsimp only
  unfold generatedTenthSourceColumnSpinSum
  simp_rw [generatedTenth_source_pauli_cached_sign_actual]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
