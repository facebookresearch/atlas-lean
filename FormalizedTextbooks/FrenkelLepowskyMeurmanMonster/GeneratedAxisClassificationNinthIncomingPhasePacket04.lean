/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingSourceData

/-! Original preferred-Q phase certificate on incoming label block 4. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
-- Bound this actual source replay to sixty-four original incoming odd labels.
/-- Retain the actual nine-factor preferred-Q central coefficient
on every nonzero source. -/
theorem generatedNinth_incoming_phase_packet_04 : ∀ m : Fin 64,
    let d : Fin 2048 := ⟨256 + m.val, by omega⟩
    generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) ≠ 0 →
      Multiplicative.toAdd (generatedNinthQImage
        (generatedNinthIncomingShortQ (generatedNinthIncomingSource d))).coeff =
          generatedNinthIncomingPhase d := by
  have check : ∀ m : Fin 64,
    let d : Fin 2048 := ⟨256 + m.val, by omega⟩
    if generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) = 0 then True else
      Multiplicative.toAdd (generatedNinthQImage
        (generatedNinthIncomingShortQ (generatedNinthIncomingSource d))).coeff =
          generatedNinthIncomingPhase d := by
    decide +kernel
  intro m
  dsimp only
  intro hm
  have h := check m
  simpa only [ite_eq_right hm] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
