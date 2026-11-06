/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Transitivity

/-! Exact stabilizers of intrinsic actual A2 planes in the selected E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual A2-plane stabilizer inside the full genuine selected-section group. -/
def leechSeventhE8A2PlaneSectionStabilizer (W : leechSeventhE8A2Planes) :
    Subgroup leechSeventhE8SectionGroup := MulAction.stabilizer leechSeventhE8SectionGroup W

/-- The actual selected-section stabilizer of every intrinsic A2 plane has order 159252480. -/
theorem leechSeventhE8A2PlaneSectionStabilizer_card (W : leechSeventhE8A2Planes) :
    Nat.card (leechSeventhE8A2PlaneSectionStabilizer W) = 159252480 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    leechSeventhE8SectionGroup W)
  rw [Nat.card_prod, leechSeventhE8A2Planes_action_orbit_card,
    generatedAxisE8_sectionStabilizer_card generatedFifthFlagOctad] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1120)
    (h.trans (by decide : 178362777600 = 1120 * 159252480))

/-- The simultaneous selected-section and A2-plane stabilizer viewed in full actual Co0. -/
def leechSeventhE8A2FlagStabilizer (W : leechSeventhE8A2Planes) :
    Subgroup leechIsomSubgroup :=
  (leechSeventhE8A2PlaneSectionStabilizer W).map leechSeventhE8SectionGroup.subtype

/-- Full actual flag membership fixes both the selected section and the genuine real A2 plane. -/
theorem leechSeventhE8A2FlagStabilizer_mem (W : leechSeventhE8A2Planes)
    (e : leechIsomSubgroup) :
    e ∈ leechSeventhE8A2FlagStabilizer W ↔
      e ∈ leechSeventhE8SectionGroup ∧ W.val.map e.val.toLinearMap = W.val := by
  constructor
  · rintro ⟨g, hg, hge⟩
    change g.val = e at hge
    subst e
    refine ⟨g.property, ?_⟩
    change g • W = W at hg
    exact congrArg Subtype.val hg
  · rintro ⟨he, hW⟩
    exact ⟨⟨e, he⟩, Subtype.ext hW, rfl⟩

/-- The simultaneous actual selected-section and A2-plane stabilizer has order 159252480. -/
theorem leechSeventhE8A2FlagStabilizer_card (W : leechSeventhE8A2Planes) :
    Nat.card (leechSeventhE8A2FlagStabilizer W) = 159252480 := by
  rw [leechSeventhE8A2FlagStabilizer, Subgroup.card_subtype,
    leechSeventhE8A2PlaneSectionStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
