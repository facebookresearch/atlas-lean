/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhElevenFramesGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhXiTetrad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhTetradMonomialAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhProjectedFrameLower
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMatrixFixed

/-! A single genuine moving Xi projection supplies the remaining seventh spatial generation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual matrix fixers whose original Conway projection has a full-axis fixing lift. -/
def generatedSeventhSpatialAxisPreimage : Subgroup generatedSeventhSpatialStabilizer :=
  generatedSeventhProjectedAxisStabilizer.comap
    ((QuotientGroup.mk' signsSubgroup).comp generatedSeventhSpatialStabilizer.subtype)

private theorem full_frame_le :
    MulAction.stabilizer generatedSeventhSpatialStabilizer
      (leechReduction (leechCoordinateFrameLattice 0)) ≤ generatedSeventhSpatialAxisPreimage := by
  intro f hf
  exact generatedSeventh_frame_projection_mem ⟨f, hf⟩

private theorem sign_two_mem :
    golayLabelCoefficients 2 ∈ generatedSeventhSignParameterSpace := by
  rw [generatedSeventhSignParameter_mem_iff]
  decide +kernel

private theorem xi_spatial : generatedSeventhXiPlaneFiber.val.2 ∈
    generatedSeventhSpatialStabilizer := by
  change conwayMatrixAction generatedSeventhXiPlaneFiber.val.2
    (griessConwayEncode generatedSeventhAxis).1 = _
  rw [generatedSeventh_axis_matrix]
  exact generatedSeventhXiPlane_matrix_fixed

/-- Assuming only the full-axis projection of the actual moving Xi, all eleven stated genuine
frame classes lie in the actual lifted-projection preimage orbit. -/
theorem generatedSeventhElevenFrameProjection_orbit
    (hx : QuotientGroup.mk' signsSubgroup generatedSeventhXiPlaneFiber.val.2 ∈
      generatedSeventhProjectedAxisStabilizer)
    (a : Option leechSeventhTetradParameter) :
    leechSeventhElevenFrameClass a ∈ MulAction.orbit generatedSeventhSpatialAxisPreimage
      (leechReduction (leechCoordinateFrameLattice 0)) := by
  cases a with
  | none => exact ⟨1, one_smul _ _⟩
  | some a =>
    obtain ⟨p, hp⟩ := generatedSeventh_triangle_five_transitive 15 a.1.val
      (by decide +kernel) a.1.property
    let pK : generatedSeventhSpatialAxisPreimage :=
      ⟨⟨golayPermutationIsometry p.val,
        generatedSeventh_triangle_permutation_spatial p.val p.property⟩,
        generatedSeventh_permutation_mem_projected p.val p.property⟩
    let sK : generatedSeventhSpatialAxisPreimage :=
      ⟨⟨golaySignIsometry (sourceGeneratedSignCode 2),
        (generatedSeventh_sign_spatial_mem_iff 2).mpr
          ((generatedSeventhSignParameter_mem_iff _).mp sign_two_mem)⟩,
        generatedSeventh_sign_mem_projected 2 sign_two_mem⟩
    let xK : generatedSeventhSpatialAxisPreimage := ⟨⟨_, xi_spatial⟩, hx⟩
    let bK : generatedSeventhSpatialAxisPreimage := if a.2 then sK else 1
    refine ⟨pK * bK * xK, ?_⟩
    have hval : (pK * bK * xK).val.val =
        golayPermutationIsometry p.val *
          (if a.2 then golaySignIsometry (sourceGeneratedSignCode 2) else 1) *
            generatedSeventhXiPlaneFiber.val.2 := by
      dsimp only [pK, bK, sK, xK]
      split_ifs <;> rfl
    change leechModTwoAction (pK * bK * xK).val.val
      (leechReduction (leechCoordinateFrameLattice 0)) = leechSeventhTetradClass a
    rw [hval]
    rw [map_mul, map_mul]
    change leechModTwoAction (golayPermutationIsometry p.val)
      (leechModTwoAction (if a.2 then golaySignIsometry (sourceGeneratedSignCode 2) else 1)
        (leechModTwoAction generatedSeventhXiPlaneFiber.val.2
          (leechReduction (leechCoordinateFrameLattice 0)))) = _
    rw [leechSeventhXiTetrad_frame_class]
    rcases a with ⟨t, b⟩
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, map_one]
      exact leechSeventhTetrad_permutation p t hp false
    | true =>
      simp only [↓reduceIte]
      rw [leechSeventhTetrad_source_sign]
      exact leechSeventhTetrad_permutation p t hp true

/-- The one actual moving-Xi projection forces equality
with the full original spatial projection. -/
theorem generatedSeventh_projection_eq_spatial_of_xi
    (hx : QuotientGroup.mk' signsSubgroup generatedSeventhXiPlaneFiber.val.2 ∈
      generatedSeventhProjectedAxisStabilizer) :
    generatedSeventhProjectedAxisStabilizer = generatedSeventhCo1SpatialStabilizer := by
  have htop : generatedSeventhSpatialAxisPreimage = ⊤ :=
    generatedSeventhSpatial_eq_top_of_eleven_frames _ full_frame_le
      (generatedSeventhSpatial_eleven_frames_orbit_lower _
        (generatedSeventhElevenFrameProjection_orbit hx))
  apply le_antisymm generatedSeventhProjectedAxisStabilizer_le_spatial
  rintro e ⟨f, hf, rfl⟩
  have h : (⟨f, hf⟩ : generatedSeventhSpatialStabilizer) ∈
      generatedSeventhSpatialAxisPreimage := by rw [htop]; trivial
  exact h

/-- The remaining actual moving-Xi projection yields
the full original local-axis stabilizer order. -/
theorem generatedSeventh_local_stabilizer_card_of_xi
    (hx : QuotientGroup.mk' signsSubgroup generatedSeventhXiPlaneFiber.val.2 ∈
      generatedSeventhProjectedAxisStabilizer) :
    Nat.card generatedSeventhLocalAxisStabilizer = 318504960 := by
  rw [generatedSeventh_local_stabilizer_card_range,
    generatedSeventh_projection_eq_spatial_of_xi hx, generatedSeventhCo1SpatialStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
