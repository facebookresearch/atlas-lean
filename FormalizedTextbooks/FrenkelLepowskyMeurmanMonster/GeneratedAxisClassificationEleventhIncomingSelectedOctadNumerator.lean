/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSelectedOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthPacketNumerator

/-! Exact executable integer numerators of all complete actual incoming selected octad rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times every actual selected octad coordinate after the genuine root-3 local word. -/
def generatedEleventhIncomingSelectedOctadNumerator (s : Fin 10) (p : Fin 64) : ℤ :=
  if h : generatedEleventhSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩ < 4136 then
    let n : Fin 4136 := ⟨generatedEleventhSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩, h⟩
    generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n) *
      (if generatedEleventhIncomingShortPhase n = 0 then 1 else -1)
  else 0

/-- Every original incoming selected octad row equals its executable signed integer numerator. -/
theorem generatedEleventh_incoming_selected_octad_numerator (s : Fin 10) (p : Fin 64) :
    (griessConwayEncode (rhoLocal generatedEleventhLocal generatedFifthAxis)).2.1 (Sum.inr
        (Sum.inl (generatedEleventhSelectedShortOctad s, p))) =
      (generatedEleventhIncomingSelectedOctadNumerator s p : ℝ) / 16 := by
  rw [generatedEleventh_incoming_selected_octad_coordinate,
      generatedEleventhIncomingSelectedOctadNumerator]
  split_ifs with h
  · dsimp only
    let n : Fin 4136 := ⟨generatedEleventhSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩, h⟩
    have hp : generatedAxisGlobalFifthRoot03ShortPhase
        (generatedAxisGlobalFifthPacketFromNumber n) = generatedEleventhIncomingShortPhase n := by
      change generatedEleventhIncomingShortPhase
        (generatedAxisGlobalFifthPacketNumber (generatedAxisGlobalFifthPacketFromNumber n)) = _
      rw [generatedAxisGlobalFifthPacketNumber_fromNumber]
    rw [generatedTenth_packet_coefficient_numerator]
    change ((generatedTenthPacketNumerator
      (generatedAxisGlobalFifthPacketFromNumber n) : ℝ) / 16) *
      qSign (generatedAxisGlobalFifthRoot03ShortPhase
        (generatedAxisGlobalFifthPacketFromNumber n)) = _
    rw [hp]
    simp only [Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg, qSign]
    ring
  · simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
