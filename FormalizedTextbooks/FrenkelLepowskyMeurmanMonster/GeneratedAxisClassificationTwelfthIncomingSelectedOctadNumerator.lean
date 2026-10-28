/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSelectedOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthPacketNumerator

/-! Exact executable integer numerators of all complete actual incoming selected octad rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times every actual selected octad coordinate after the genuine root-9 local word. -/
def generatedTwelfthIncomingSelectedOctadNumerator (s : Fin 12) (p : Fin 64) : ℤ :=
  if h : generatedTwelfthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩ < 4136 then
    let n : Fin 4136 := ⟨generatedTwelfthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩, h⟩
    generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n) *
      (if generatedTwelfthIncomingShortPhase n = 0 then 1 else -1)
  else 0

/-- Every original incoming selected octad row equals its executable signed integer numerator. -/
theorem generatedTwelfth_incoming_selected_octad_numerator (s : Fin 12) (p : Fin 64) :
    (griessConwayEncode (rhoLocal generatedTwelfthLocal generatedFifthAxis)).2.1 (Sum.inr (Sum.inl
        (generatedTwelfthSelectedShortOctad s, p))) =
      (generatedTwelfthIncomingSelectedOctadNumerator s p : ℝ) / 16 := by
  rw [generatedTwelfth_incoming_selected_octad_coordinate,
      generatedTwelfthIncomingSelectedOctadNumerator]
  split_ifs with h
  · dsimp only
    let n : Fin 4136 := ⟨generatedTwelfthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩, h⟩
    have hp : generatedAxisGlobalFifthRoot09ShortPhase
        (generatedAxisGlobalFifthPacketFromNumber n) = generatedTwelfthIncomingShortPhase n := by
      change generatedTwelfthIncomingShortPhase
        (generatedAxisGlobalFifthPacketNumber (generatedAxisGlobalFifthPacketFromNumber n)) = _
      rw [generatedAxisGlobalFifthPacketNumber_fromNumber]
    rw [generatedTenth_packet_coefficient_numerator]
    change ((generatedTenthPacketNumerator
      (generatedAxisGlobalFifthPacketFromNumber n) : ℝ) / 16) *
      qSign (generatedAxisGlobalFifthRoot09ShortPhase
        (generatedAxisGlobalFifthPacketFromNumber n)) = _
    rw [hp]
    simp only [Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg, qSign]
    ring
  · simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
