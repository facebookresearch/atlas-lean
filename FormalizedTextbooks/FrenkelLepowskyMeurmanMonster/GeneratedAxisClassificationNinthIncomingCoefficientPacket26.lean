/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingSourceData

/-! Original preferred-Q coefficient certificate on incoming label block 26. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
-- Bound this actual source replay to sixty-four original incoming odd labels.
/-- The candidate signed coefficient is the true finite original source numerator. -/
theorem generatedNinth_incoming_coefficient_packet_26 : ∀ m : Fin 64,
    let d : Fin 2048 := ⟨1664 + m.val, by omega⟩
    (if generatedNinthIncomingPhase d = 0 then (1 : ℤ) else -1) *
      generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) =
        generatedNinthIncomingCoefficient d := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
