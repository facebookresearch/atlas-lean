/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPacket
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQFast

/-! Executable original preferred-Q lifts of the entire actual fifth short packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The octad's negative positions use its already checked eight physical coordinates. -/
def generatedAxisGlobalFifthShortNegativeInteger (j : Fin 56) (e : Fin 64)
    (i : Fin 24) : ℤ :=
  if ((List.finRange 8).foldr (fun (k : Fin 8) (m : ℕ) =>
      (if (trialityEvenMask e).testBit k.val then
        2 ^ (generatedFifthEvenRootCoordinates j k).val else 0) ||| m) 0).testBit i.val
    then 1 else 0

/-- The executable negative-position vector equals the intrinsic actual octad vector. -/
theorem generatedAxisGlobalFifthShortNegativeInteger_actual (j : Fin 56) (e : Fin 64) :
    generatedAxisGlobalFifthShortNegativeInteger j e =
      griessOctadNegativeInteger (generatedFifthEvenRootOctad j) e := by
  funext i
  unfold generatedAxisGlobalFifthShortNegativeInteger griessOctadNegativeInteger
    griessOctadSignMask
  simp_rw [generatedFifth_even_coordinates_certificate]

/-- The full original preferred lift, including its signed-octad Ω correction. -/
def generatedAxisGlobalFifthShortPacketQ : GeneratedAxisGlobalFifthShortPacketIndex → Q
  | Sum.inl p => monsterNortonShortQSource (Sum.inl p)
  | Sum.inr (j, e) =>
      ⟨ofAdd (Fin.append
        (golayLabelCoefficients (generatedFifthEvenRootCode j) +
          griessOctadOmegaCoefficient e • Pi.single 11 1)
        (sourceWordTheta (generatedFifthEvenRootCode j) +
          golaySyndrome (integerParity (generatedAxisGlobalFifthShortNegativeInteger j e)))), 1⟩

/-- The finite source formula is the entire genuine preferred-Q lift of each packet entry. -/
theorem generatedAxisGlobalFifthShortPacketQ_actual
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthShortPacketQ i =
      griessShortQ (generatedAxisGlobalFifthShortPacketLabel i) := by
  rcases i with p | ⟨j, e⟩
  · exact monsterNortonShortQSource_actual (Sum.inl p)
  · rw [← monsterNortonShortQSource_actual]
    change _ = monsterNortonShortQSource (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e)))
    simp only [generatedAxisGlobalFifthShortPacketQ, monsterNortonShortQSource,
      monsterNortonShortTranslation, monsterNortonShortModulation]
    rw [generatedFifthEvenRootOctad_label, generatedAxisGlobalFifthShortNegativeInteger_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
