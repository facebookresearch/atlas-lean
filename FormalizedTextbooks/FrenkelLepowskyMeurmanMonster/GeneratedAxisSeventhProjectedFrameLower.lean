/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhFrameOrbitExact

/-! Full-axis lifts of every genuine spatial frame fixer and the resulting cardinal lower bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The previously counted sign-permutation elements exhaust the actual spatial frame stabilizer. -/
theorem generatedSeventhMonomialSpatialFrameMap_surjective :
    Function.Surjective generatedSeventhMonomialSpatialFrameMap := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  apply (Nat.bijective_iff_injective_and_card _).mpr
    ⟨generatedSeventhMonomialSpatialFrameMap_injective, ?_⟩ |>.2
  rw [Nat.card_prod, generatedSeventhSignParameterSpace_card,
    generatedSeventh_triangle_permutation_card, generatedSeventh_spatial_frame_stabilizer_card]

/-- Every genuine seventh spatial frame fixer has a full-axis fixing Conway projection. -/
theorem generatedSeventh_frame_projection_mem
    (f : MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0))) :
    QuotientGroup.mk' signsSubgroup f.val.val ∈ generatedSeventhProjectedAxisStabilizer := by
  obtain ⟨⟨a, p⟩, rfl⟩ := generatedSeventhMonomialSpatialFrameMap_surjective f
  change QuotientGroup.mk' signsSubgroup
    (golaySignIsometry (generatedSeventhSpatialSignCode a) * golayPermutationIsometry p.val) ∈ _
  rw [map_mul]
  apply generatedSeventhProjectedAxisStabilizer.mul_mem
  · apply generatedSeventhProjectedSignSubgroup_le_axis
    exact ⟨_, ⟨Multiplicative.ofAdd a, rfl⟩, rfl⟩
  · exact generatedSeventh_permutation_mem_projected p.val p.property

/-- Restricting the actual quotient map to actual spatial frame fixers lands in the full axis group. -/
def generatedSeventhFrameProjectionHom :
    MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0)) →*
      generatedSeventhProjectedAxisStabilizer :=
  ((QuotientGroup.mk' signsSubgroup).comp
    (generatedSeventhSpatialStabilizer.subtype.comp
      (MulAction.stabilizer generatedSeventhSpatialStabilizer
        (leechReduction (leechCoordinateFrameLattice 0))).subtype)).codRestrict _
    generatedSeventh_frame_projection_mem

/-- The only possible kernel elements of the spatial frame projection are the two real signs. -/
theorem generatedSeventhFrameProjectionHom_kernel_card_le :
    Nat.card generatedSeventhFrameProjectionHom.ker ≤ 2 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let f : generatedSeventhFrameProjectionHom.ker → signsSubgroup := fun x =>
    ⟨x.val.val.val, by
      have hx := congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
      change (QuotientGroup.mk (x.val.val.val) : Co1) = 1 at hx
      exact (QuotientGroup.eq_one_iff _).mp hx⟩
  have hi : Function.Injective f := by
    intro a b h
    have he : a.val.val.val = b.val.val.val :=
      congrArg (fun x : signsSubgroup => x.val) h
    exact Subtype.ext (Subtype.ext (Subtype.ext he))
  have h := Nat.card_le_card_of_injective f hi
  rwa [signsSubgroup_card] at h

/-- The actual full-axis Conway projection contains at least 2949120 distinct frame-fixing values. -/
theorem generatedSeventhProjectedAxisStabilizer_frame_card_ge :
    2949120 ≤ Nat.card generatedSeventhProjectedAxisStabilizer := by
  let : Finite Co1 := co1_finite
  have h := generatedSeventhFrameProjectionHom.ker.card_mul_index
  rw [Subgroup.index_ker, generatedSeventh_spatial_frame_stabilizer_card] at h
  have hk := generatedSeventhFrameProjectionHom_kernel_card_le
  have hr := Nat.card_le_card_of_injective
    generatedSeventhFrameProjectionHom.range.subtype
    generatedSeventhFrameProjectionHom.range.subtype_injective
  nlinarith

/-- Its proved four-element Q kernel supplies at least 11796480 actual local-axis fixers. -/
theorem generatedSeventhLocalAxisStabilizer_frame_card_ge :
    11796480 ≤ Nat.card generatedSeventhLocalAxisStabilizer := by
  rw [generatedSeventh_local_stabilizer_card_range]
  exact Nat.mul_le_mul_left 4 generatedSeventhProjectedAxisStabilizer_frame_card_ge

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
