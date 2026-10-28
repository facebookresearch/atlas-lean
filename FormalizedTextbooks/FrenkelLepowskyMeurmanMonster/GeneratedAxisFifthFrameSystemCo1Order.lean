/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemOrder

/-! Exact cardinality of the actual fifth section/system stabilizer in the central-sign quotient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The full actual section/system stabilizer projected into the original quotient Co1. -/
def generatedFifthFrameSystemCo1Stabilizer : Subgroup Co1 :=
  generatedFifthFrameSystemStabilizer.map (QuotientGroup.mk' signsSubgroup)

/-- The full actual simultaneous stabilizer has its exact index in Co0. -/
theorem generatedFifthFrameSystem_stabilizer_index :
    generatedFifthFrameSystemStabilizer.index = 6293912625 := by
  have h := generatedFifthFrameSystemStabilizer.card_mul_index
  rw [generatedFifthFrameSystem_stabilizer_card, co0_card_exact] at h
  omega

/-- Passing to the original central-sign quotient preserves the full actual subgroup index. -/
theorem generatedFifthFrameSystem_co1_stabilizer_index :
    generatedFifthFrameSystemCo1Stabilizer.index = 6293912625 := by
  change (generatedFifthFrameSystemStabilizer.map
    (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedFifthFrameSystem_stabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedAxisE8FrameSystemStabilizer_signs_le _ _

/-- The genuine projected fifth section/system stabilizer has exact order660602880. -/
theorem generatedFifthFrameSystem_co1_stabilizer_card :
    Nat.card generatedFifthFrameSystemCo1Stabilizer = 660602880 := by
  have h := generatedFifthFrameSystemCo1Stabilizer.card_mul_index
  rw [generatedFifthFrameSystem_co1_stabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 6293912625)
    (h.trans (by decide : 4157776806543360000 = 660602880 * 6293912625))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
