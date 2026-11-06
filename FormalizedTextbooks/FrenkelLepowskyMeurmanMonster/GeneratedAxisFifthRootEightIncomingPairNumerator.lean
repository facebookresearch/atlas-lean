/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightPairCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightPacketNumerator

/-! Exact executable integer numerators of all complete actual incoming pair rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times every actual pair coordinate after the genuine root-8 local word. -/
def generatedFifthRootEightIncomingPairNumerator (s : Fin 2) (p : Fin 276) : ℤ :=
  if h : generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136 then
    let n : Fin 4136 := ⟨generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩
    generatedFifthRootEightPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n) *
      (if generatedFifthRootEightIncomingShortPhase n = 0 then 1 else -1)
  else 0

/-- Every original incoming pair row equals its executable signed integer numerator. -/
theorem generatedFifthRootEight_incoming_pair_numerator (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)).2.1 (Sum.inl
      (s, p)) =
      (generatedFifthRootEightIncomingPairNumerator s p : ℝ) / 16 := by
  rw [generatedFifthRootEight_incoming_pair_coordinate,
    generatedFifthRootEightIncomingPairNumerator]
  split_ifs with h
  · dsimp only
    let n : Fin 4136 := ⟨generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩
    have hp : generatedAxisGlobalFifthRoot08ShortPhase
        (generatedAxisGlobalFifthPacketFromNumber n) = generatedFifthRootEightIncomingShortPhase n
          := by
      change generatedFifthRootEightIncomingShortPhase
        (generatedAxisGlobalFifthPacketNumber (generatedAxisGlobalFifthPacketFromNumber n)) = _
      rw [generatedAxisGlobalFifthPacketNumber_fromNumber]
    rw [generatedFifthRootEight_packet_coefficient_numerator]
    change ((generatedFifthRootEightPacketNumerator
      (generatedAxisGlobalFifthPacketFromNumber n) : ℝ) / 16) *
      qSign (generatedAxisGlobalFifthRoot08ShortPhase
        (generatedAxisGlobalFifthPacketFromNumber n)) = _
    rw [hp]
    simp only [Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg, qSign]
    ring
  · simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
