/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemCo1Order

/-! The second genuine system stabilizer in the original central-sign quotient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Candidate zero's full actual simultaneous stabilizer has index 6293912625 in Co0. -/
theorem generatedAxisE8FrameSystemCandidate_zero_stabilizer_index :
    (generatedAxisE8FrameSystemStabilizer generatedFifthFlagOctad
      (generatedAxisE8ActualFrameSystemCandidate 0)).index = 6293912625 := by
  have h := (generatedAxisE8FrameSystemStabilizer generatedFifthFlagOctad
    (generatedAxisE8ActualFrameSystemCandidate 0)).card_mul_index
  rw [generatedAxisE8FrameSystemCandidate_zero_stabilizer_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1321205760)
    (h.trans (by decide : 8315553613086720000 = 1321205760 * 6293912625))

/-- The second genuine system stabilizer retains its index in the original Co1 quotient. -/
theorem generatedAxisE8FrameSystemCandidate_zero_co1_stabilizer_index :
    (generatedAxisE8FrameSystemCo1Stabilizer generatedFifthFlagOctad
      (generatedAxisE8ActualFrameSystemCandidate 0)).index = 6293912625 := by
  change ((generatedAxisE8FrameSystemStabilizer generatedFifthFlagOctad
    (generatedAxisE8ActualFrameSystemCandidate 0)).map
      (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedAxisE8FrameSystemCandidate_zero_stabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedAxisE8FrameSystemStabilizer_signs_le _ _

/-- Candidate zero's full genuine projected simultaneous stabilizer has order 660602880. -/
theorem generatedAxisE8FrameSystemCandidate_zero_co1_stabilizer_card :
    Nat.card (generatedAxisE8FrameSystemCo1Stabilizer generatedFifthFlagOctad
      (generatedAxisE8ActualFrameSystemCandidate 0)) = 660602880 := by
  have h := (generatedAxisE8FrameSystemCo1Stabilizer generatedFifthFlagOctad
    (generatedAxisE8ActualFrameSystemCandidate 0)).card_mul_index
  rw [generatedAxisE8FrameSystemCandidate_zero_co1_stabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 6293912625)
    (h.trans (by decide : 4157776806543360000 = 660602880 * 6293912625))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
