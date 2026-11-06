/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhFrameOrbitExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhTetradClasses

/-! Eleven actual frame images force generation
once the whole actual frame stabilizer is present. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A subgroup containing the whole actual frame stabilizer and eleven frame images is the whole
seventh spatial group. The conclusion uses its proved orbit cardinality twenty-seven. -/
theorem generatedSeventhSpatial_eq_top_of_eleven_frames
    (K : Subgroup generatedSeventhSpatialStabilizer)
    (hframe : MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0)) ≤ K)
    (horbit : 11 ≤ Nat.card (MulAction.orbit K
      (leechReduction (leechCoordinateFrameLattice 0)))) : K = ⊤ := by
  let P := MulAction.stabilizer generatedSeventhSpatialStabilizer
    (leechReduction (leechCoordinateFrameLattice 0))
  have hP : P.index = 27 := by
    change (MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0))).index = 27
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact generatedSeventh_spatial_frame_orbit_card
  have hstab : P.subgroupOf K = MulAction.stabilizer K
      (leechReduction (leechCoordinateFrameLattice 0)) := by
    ext k
    rfl
  have hrel : P.relIndex K = Nat.card (MulAction.orbit K
      (leechReduction (leechCoordinateFrameLattice 0))) := by
    rw [Subgroup.relIndex, hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hmul := P.relIndex_mul_index hframe
  rw [hP] at hmul
  have hlo : 11 ≤ P.relIndex K := by simpa only [hrel] using horbit
  have hn : K.index ≠ 0 := by intro hz; rw [hz, mul_zero] at hmul; norm_num at hmul
  have hle : K.index ≤ 2 := by nlinarith
  have hcases : K.index = 1 ∨ K.index = 2 := by omega
  rcases hcases with hi | hi
  · exact Subgroup.index_eq_one.mp hi
  · rw [hi] at hmul
    omega

/-- Membership of all eleven distinct original lattice classes supplies the required orbit bound. -/
theorem generatedSeventhSpatial_eleven_frames_orbit_lower
    (K : Subgroup generatedSeventhSpatialStabilizer)
    (h : ∀ a : Option leechSeventhTetradParameter,
      leechSeventhElevenFrameClass a ∈ MulAction.orbit K
        (leechReduction (leechCoordinateFrameLattice 0))) :
    11 ≤ Nat.card (MulAction.orbit K (leechReduction (leechCoordinateFrameLattice 0))) := by
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  let f : Option leechSeventhTetradParameter →
      MulAction.orbit K (leechReduction (leechCoordinateFrameLattice 0)) :=
    fun a => ⟨leechSeventhElevenFrameClass a, h a⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact leechSeventhElevenFrameClass_injective (congrArg Subtype.val hab)
  have hc := Nat.card_le_card_of_injective f hf
  rwa [leechSeventhElevenFrameClass_domain_card] at hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
