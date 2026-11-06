/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7NormalLine
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7FrameRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitAction

/-! The entire actual root anchor stabilizer consists of genuine Golay monomial isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original anchored root has actual integer square sum32. -/
theorem generatedTenth_e7_anchor_root_square :
    leechSquareSum (generatedTenthE7OrbitNodeRoot 0).val = 32 :=
  generatedTenth_e7_standard_e8_root_square _

/-- The sum of the two original normal and anchor roots is the fourth coordinate frame. -/
theorem generatedTenth_e7_anchor_frame_four :
    generatedTenthE7OrbitNormalRoot + generatedTenthE7OrbitNodeRoot 0 =
      leechCoordinateFrameLattice 4 := by
  apply Subtype.ext
  change generatedTenthE7OrbitNormalRoot.val + (generatedTenthE7OrbitNodeRoot 0).val = _
  rw [generatedTenth_e7_orbit_node_physical]
  decide +kernel

/-- Their difference is the fifth actual coordinate frame. -/
theorem generatedTenth_e7_anchor_frame_five :
    generatedTenthE7OrbitNormalRoot - generatedTenthE7OrbitNodeRoot 0 =
      leechCoordinateFrameLattice 5 := by
  apply Subtype.ext
  change generatedTenthE7OrbitNormalRoot.val - (generatedTenthE7OrbitNodeRoot 0).val = _
  rw [generatedTenth_e7_orbit_node_physical]
  decide +kernel

/-- A genuine short-class anchor fixer sends its original root to one of its two orientations. -/
theorem generatedTenth_e7_anchor_class_sign (g : leechIsomSubgroup)
    (hg : leechModTwoAction g (generatedTenthE7OrbitNodeClass 0) =
      generatedTenthE7OrbitNodeClass 0) :
    leechIntegralAction g (generatedTenthE7OrbitNodeRoot 0) = generatedTenthE7OrbitNodeRoot 0 ∨
      leechIntegralAction g (generatedTenthE7OrbitNodeRoot 0) =
        -generatedTenthE7OrbitNodeRoot 0 := by
  apply leechShort_same_class
  · rw [leechIntegralAction_squareSum, generatedTenth_e7_anchor_root_square]
  · exact generatedTenth_e7_anchor_root_square
  · exact hg

/-- Fixing the actual anchor class in the entire original matrix group forces monomiality. -/
theorem generatedTenth_e7_anchor_class_monomial (g : generatedTenthE7StandardMatrixGroup)
    (hg : leechModTwoAction g.val (generatedTenthE7OrbitNodeClass 0) =
      generatedTenthE7OrbitNodeClass 0) : g.val ∈ golayMonomialSubgroup := by
  have hn := generatedTenth_e7_matrix_normal_line g
  have hr := generatedTenth_e7_anchor_class_sign g.val hg
  have hf := congrArg (leechIntegralAction g.val) generatedTenth_e7_anchor_frame_four
  rw [map_add] at hf
  rcases hn with hn | hn <;> rcases hr with hr | hr
  · apply generatedTenth_e7_signed_frame_monomial g.val 4 4
    left
    rw [hn, hr, generatedTenth_e7_anchor_frame_four] at hf
    exact hf.symm
  · apply generatedTenth_e7_signed_frame_monomial g.val 4 5
    left
    rw [hn, hr, ← sub_eq_add_neg, generatedTenth_e7_anchor_frame_five] at hf
    exact hf.symm
  · apply generatedTenth_e7_signed_frame_monomial g.val 4 5
    right
    rw [hn, hr] at hf
    have he : -generatedTenthE7OrbitNormalRoot + generatedTenthE7OrbitNodeRoot 0 =
        -leechCoordinateFrameLattice 5 := by
      rw [← generatedTenth_e7_anchor_frame_five]
      abel
    rw [he] at hf
    exact hf.symm
  · apply generatedTenth_e7_signed_frame_monomial g.val 4 4
    right
    rw [hn, hr, ← neg_add, generatedTenth_e7_anchor_frame_four] at hf
    exact hf.symm

/-- The whole actual short-anchor stabilizer, rather than a selected generated subgroup,
is contained in the genuine Golay monomial group. -/
theorem generatedTenth_e7_anchor_stabilizer_monomial
    (g : MulAction.stabilizer generatedTenthE7StandardMatrixGroup
      (generatedTenthE7RootShortLabelEquiv 0)) : g.val.val ∈ golayMonomialSubgroup := by
  apply generatedTenth_e7_anchor_class_monomial
  have h := congrArg (fun r : generatedTenthE7RootShortSet => griessShortClass r.val) g.property
  change griessShortClass (griessShortPermutation g.val.val (generatedTenthE7OrbitNodeLabel 0)) =
    griessShortClass (generatedTenthE7OrbitNodeLabel 0) at h
  rw [griessShortPermutation_class, ← generatedTenth_e7_orbit_node_class_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
