/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- This bounded source packet checks 64 complete original row addresses and coefficients.
/-- The bounded packet preserves every original source row and its full central sign. -/
theorem generatedFifthRootEight_incoming_short_coverage_check43 : ∀ i : Fin 64,
    let k : Fin 4136 := ⟨(2752 + i.val) % 4136, Nat.mod_lt _ (by decide)⟩
    generatedFifthRootEightIncomingShortCoefficient (generatedFifthRootEightIncomingShortTarget k) =
      generatedFifthRootEightIncomingSignedRowNumerator k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
