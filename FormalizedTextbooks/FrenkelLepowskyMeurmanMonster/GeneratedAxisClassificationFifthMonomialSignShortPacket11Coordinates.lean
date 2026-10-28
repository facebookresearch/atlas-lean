/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket11Phase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortSoundness

/-! Genuine original octad-coordinate fixation by one complete corrected source sign word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- This actual corrected source sign word fixes every original outgoing octad coefficient. -/
theorem generatedFifthSignShortPacket11_coordinate (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber 11))
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        (griessConwayEncode generatedFifthAxis).2.1
          (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) := by
  apply generatedFifth_sign_short_octad_of_certificate 11 j e
    (generatedFifthSignShortPacket11Source j) (generatedFifthSignShortPacket11Correction j)
    (generatedFifthSignShortPacket11_source_phase j)
    (generatedFifthSignShortPacket11_correction_phase j)
  simpa only [generatedFifthSignShortNumerator, generatedFifthSignShortPacket11Numerator] using
    generatedFifthSignShortPacket11_numerator j e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
