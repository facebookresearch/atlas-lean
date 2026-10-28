/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! The actual sixth-axis spatial stabilizer and the proved projection bound for full fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Leech isometries fixing the original sixth-axis matrix. -/
def generatedSixthSpatialStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedSixthAxis).1 =
    (griessConwayEncode generatedSixthAxis).1}
  one_mem' := by
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change conwayMatrixAction (g * h) _ = _
    rw [map_mul]
    change conwayMatrixAction g (conwayMatrixAction h _) = _
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change conwayMatrixAction g⁻¹ _ = _
    rw [map_inv]
    change (conwayMatrixAction g).symm _ = _
    calc
      _ = (conwayMatrixAction g).symm
          (conwayMatrixAction g (griessConwayEncode generatedSixthAxis).1) := by rw [hg]
      _ = _ := LinearEquiv.symm_apply_apply _ _

/-- Membership is precisely preservation of the actual two-root plane and actual root line. -/
theorem generatedSixthSpatialStabilizer_mem (g : leechIsomSubgroup) :
    g ∈ generatedSixthSpatialStabilizer ↔
      (∀ x, x ∈ generatedSixthRootedPlane ↔ g.val x ∈ generatedSixthRootedPlane) ∧
        griessShortPermutation g generatedSixthPlaneShort = generatedSixthPlaneShort :=
  generatedSixth_axis_matrix_plane_fixed_iff g

/-- The actual spatial flag stabilizer's image in the genuine Conway quotient. -/
def generatedSixthCo1SpatialStabilizer : Subgroup Co1 :=
  generatedSixthSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)

/-- Full local fixation preserves both components of the genuine spatial flag. -/
theorem generatedSixth_local_fiber_spatial_mem (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedSixthAxis = generatedSixthAxis) :
    f.val.2 ∈ generatedSixthSpatialStabilizer := by
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix] at hm
  exact hm

/-- The full original local stabilizer of this actual axis. -/
def generatedSixthLocalAxisStabilizer : Subgroup H := MulAction.stabilizer H generatedSixthAxis

/-- The genuine restricted Conway projection of the actual sixth-axis stabilizer. -/
def generatedSixthLocalAxisProjection : generatedSixthLocalAxisStabilizer →* Co1 :=
  projH.comp generatedSixthLocalAxisStabilizer.subtype

/-- The actual projection image, without a surjectivity or order assertion. -/
def generatedSixthProjectedAxisStabilizer : Subgroup Co1 :=
  generatedSixthLocalAxisProjection.range

/-- Every full-axis projection belongs to the actual rooted-plane flag stabilizer. -/
theorem generatedSixthProjectedAxisStabilizer_le_spatial :
    generatedSixthProjectedAxisStabilizer ≤ generatedSixthCo1SpatialStabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedSixthAxis = generatedSixthAxis := by
    rw [hf]
    exact h.property
  refine ⟨f.val.2, generatedSixth_local_fiber_spatial_mem f hfix, ?_⟩
  change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
  rw [← hf]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
