/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket10Phase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortSoundness

/-! Genuine original octad-coordinate fixation by one complete corrected source sign word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- This actual corrected source sign word fixes every original outgoing octad coefficient. -/
theorem generatedFifthSignShortPacket10_coordinate (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber 10))
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        (griessConwayEncode generatedFifthAxis).2.1
          (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) := by
  apply generatedFifth_sign_short_octad_of_certificate 10 j e
    (generatedFifthSignShortPacket10Source j) (generatedFifthSignShortPacket10Correction j)
    (generatedFifthSignShortPacket10_source_phase j)
    (generatedFifthSignShortPacket10_correction_phase j)
  simpa only [generatedFifthSignShortNumerator, generatedFifthSignShortPacket10Numerator] using
    generatedFifthSignShortPacket10_numerator j e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
