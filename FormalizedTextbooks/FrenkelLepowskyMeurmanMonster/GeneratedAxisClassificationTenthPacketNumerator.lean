/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPacket

/-! Original integer coefficients of the entire fifth input packet,
for actual further transitions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times each genuine starting packet coefficient, with its original physical signs. -/
def generatedTenthPacketNumerator : GeneratedAxisGlobalFifthShortPacketIndex → ℤ
  | Sum.inl (s, p) => generatedFifthFinalPairNumerator s
      (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2
  | Sum.inr (j, e) => generatedFifthFinalOctadNumerator j e

/-- Every original packet coefficient has its exact integer numerator and physical normalization. -/
theorem generatedTenth_packet_coefficient_numerator (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthShortPacketCoefficient i =
      (generatedTenthPacketNumerator i : ℝ) / 16 := by
  rcases i with ⟨s, p⟩ | ⟨j, e⟩
  · rw [generatedTenthPacketNumerator, generatedAxisGlobalPairCoordinates_actual]
    fin_cases s
    · exact (generatedAxisGlobalFifthRaw_pair_minus p).symm.trans
        (generatedFifth_final_pair_numerator 0 p)
    · exact (generatedAxisGlobalFifthRaw_pair_plus p).symm.trans
        (generatedFifth_final_pair_numerator 1 p)
  · exact (generatedFifth_final_octad_coordinate j e).symm.trans
      (generatedFifth_final_octad_numerator j e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
