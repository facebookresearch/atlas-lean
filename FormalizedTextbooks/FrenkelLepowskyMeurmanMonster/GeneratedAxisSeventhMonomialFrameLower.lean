/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTrianglePermutationGroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSpatialSignGroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialFrameCount

/-! Genuine sign-permutation elements in the actual seventh matrix/frame stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Original ten-parameter signs and triangle permutations give actual matrix/frame fixers. -/
def generatedSeventhMonomialSpatialFrameMap
    (a : generatedSeventhSignParameterSpace × generatedSeventhTrianglePermutationSubgroup) :
    MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0)) := by
  let d := generatedSeventhSpatialSignCode a.1
  let e := golayMonomialPair (d, a.2.val)
  have hd : golaySignIsometry d ∈ generatedSeventhSpatialStabilizer :=
    generatedSeventhSpatialSignHom_mem (ofAdd a.1)
  have he : e ∈ generatedSeventhSpatialStabilizer :=
    generatedSeventhSpatialStabilizer.mul_mem hd
      (generatedSeventh_triangle_permutation_spatial a.2.val a.2.property)
  refine ⟨⟨e, he⟩, ?_⟩
  change leechModTwoAction e (leechReduction (leechCoordinateFrameLattice 0)) = _
  exact generatedFourthFlagMonomial_frame_fixed e ⟨d, a.2.val, rfl⟩

/-- Distinct actual sign parameters and permutations remain distinct physical elements. -/
theorem generatedSeventhMonomialSpatialFrameMap_injective :
    Function.Injective generatedSeventhMonomialSpatialFrameMap := by
  intro a b h
  have he := congrArg (fun u : MulAction.stabilizer generatedSeventhSpatialStabilizer
    (leechReduction (leechCoordinateFrameLattice 0)) => u.val.val) h
  have hab := golayMonomialPair_injective he
  apply Prod.ext
  · apply Subtype.ext
    apply golayEncoder_injective
    exact congrArg Subtype.val (congrArg Prod.fst hab)
  · apply Subtype.ext
    exact congrArg Prod.snd hab

/-- At least 5898240 genuine seventh matrix fixers also preserve the actual coordinate frame. -/
theorem generatedSeventh_spatial_frame_stabilizer_card_ge :
    5898240 ≤ Nat.card (MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0))) := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h := Nat.card_le_card_of_injective generatedSeventhMonomialSpatialFrameMap
    generatedSeventhMonomialSpatialFrameMap_injective
  rw [Nat.card_prod, generatedSeventhSignParameterSpace_card,
    generatedSeventh_triangle_permutation_card] at h
  exact h

/-- The full actual seventh matrix subgroup has at most 27 coordinate-frame images. -/
theorem generatedSeventh_spatial_frame_orbit_card_le :
    Nat.card (MulAction.orbit generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0))) ≤ 27 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedSeventhSpatialStabilizer (leechReduction (leechCoordinateFrameLattice 0)))
  rw [Nat.card_prod, generatedSeventhSpatialStabilizer_card] at h
  have hlo := generatedSeventh_spatial_frame_stabilizer_card_ge
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
