/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairTransitivity

/-! The actual simultaneous root and norm-six point stabilizer in the original Conway group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine positive-root subgroup includes in the original integral Conway group. -/
def leechNormSixPairPositiveInclusion : leechRootedA2PositiveRootSubgroup →* leechIsomSubgroup :=
  leechRootedA2RootLineSubgroup.subtype.comp leechRootedA2PositiveRootSubgroup.subtype

/-- The original subgroup inclusion is injective at both subtype levels. -/
theorem leechNormSixPairPositiveInclusion_injective :
    Function.Injective leechNormSixPairPositiveInclusion := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

/-- The actual simultaneous point stabilizer, viewed in the original full Conway group. -/
def leechNormSixPairPointStabilizer (u : LeechNormSixPair) : Subgroup leechIsomSubgroup :=
  (MulAction.stabilizer leechRootedA2PositiveRootSubgroup u).map leechNormSixPairPositiveInclusion

/-- Membership fixes both genuine lattice vectors pointwise, with their original signs. -/
theorem leechNormSixPairPointStabilizer_mem (u : LeechNormSixPair) (g : leechIsomSubgroup) :
    g ∈ leechNormSixPairPointStabilizer u ↔
      leechIntegralAction g leechRootedA2Root = leechRootedA2Root ∧
        leechIntegralAction g u.val = u.val := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haroot : leechIntegralAction a.val.val leechRootedA2Root = leechRootedA2Root :=
      a.property
    have hau : a • u = u := ha
    exact ⟨haroot, congrArg Subtype.val hau⟩
  · rintro ⟨hroot, hu⟩
    let a : leechRootedA2PositiveRootSubgroup :=
      ⟨⟨g, (leechRootedA2RootLineSubgroup_mem _).mpr (Or.inl hroot)⟩, hroot⟩
    exact ⟨a, (show a • u = u from Subtype.ext hu), rfl⟩

/-- The full original Conway simultaneous point stabilizer has exactly44352000 elements. -/
theorem leechNormSixPairPointStabilizer_card (u : LeechNormSixPair) :
    Nat.card (leechNormSixPairPointStabilizer u) = 44352000 := by
  rw [leechNormSixPairPointStabilizer,
    Subgroup.card_map_of_injective leechNormSixPairPositiveInclusion_injective,
    leechNormSixPair_stabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
