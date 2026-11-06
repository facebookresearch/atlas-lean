/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMatrixRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! The actual seventh-axis spatial stabilizer and the proved projection bound for full fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Leech isometries fixing the original seventh-axis matrix. -/
def generatedSeventhSpatialStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedSeventhAxis).1 =
    (griessConwayEncode generatedSeventhAxis).1}
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
          (conwayMatrixAction g (griessConwayEncode generatedSeventhAxis).1) := by rw [hg]
      _ = _ := LinearEquiv.symm_apply_apply _ _

/-- Membership is preservation of the two supports recovered from the original matrix.
No coordinate-set, root-line, projected-order, or full-axis sufficiency hypothesis is assumed. -/
theorem generatedSeventhSpatialStabilizer_mem (g : leechIsomSubgroup) :
    g ∈ generatedSeventhSpatialStabilizer ↔
      conwayMatrixAction g generatedSeventhPlaneSupport = generatedSeventhPlaneSupport ∧
        conwayMatrixAction g generatedSeventhSixSupport = generatedSeventhSixSupport :=
  generatedSeventh_axis_matrix_support_fixed_iff g

/-- The actual spatial flag stabilizer's image in the genuine Conway quotient. -/
def generatedSeventhCo1SpatialStabilizer : Subgroup Co1 :=
  generatedSeventhSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)

/-- Full local fixation preserves both intrinsic supports of the actual matrix. -/
theorem generatedSeventh_local_fiber_spatial_mem (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedSeventhAxis = generatedSeventhAxis) :
    f.val.2 ∈ generatedSeventhSpatialStabilizer := by
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix] at hm
  exact hm

/-- The full original local stabilizer of this actual axis. -/
def generatedSeventhLocalAxisStabilizer : Subgroup H := MulAction.stabilizer H generatedSeventhAxis

/-- The genuine restricted Conway projection of the actual seventh-axis stabilizer. -/
def generatedSeventhLocalAxisProjection : generatedSeventhLocalAxisStabilizer →* Co1 :=
  projH.comp generatedSeventhLocalAxisStabilizer.subtype

/-- The actual projection image, without a surjectivity or order assertion. -/
def generatedSeventhProjectedAxisStabilizer : Subgroup Co1 :=
  generatedSeventhLocalAxisProjection.range

/-- Every full-axis projection belongs to the actual two-support stabilizer. -/
theorem generatedSeventhProjectedAxisStabilizer_le_spatial :
    generatedSeventhProjectedAxisStabilizer ≤ generatedSeventhCo1SpatialStabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedSeventhAxis = generatedSeventhAxis := by
    rw [hf]
    exact h.property
  refine ⟨f.val.2, generatedSeventh_local_fiber_spatial_mem f hfix, ?_⟩
  change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
  rw [← hf]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
