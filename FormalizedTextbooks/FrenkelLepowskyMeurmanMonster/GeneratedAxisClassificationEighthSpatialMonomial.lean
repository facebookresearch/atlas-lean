/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMatrixRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderFrameOrbit

/-! Fixing the actual eighth matrix forces a genuine signed Golay permutation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual norm-eight coordinate vector has the indicated line projection. -/
theorem generatedEighth_coordinate_frame_outer :
    generatedNormEightLineMatrix (leechSignedFrame (20, 0)) =
      (8 : ℝ) • generatedEighthCoordinateLineProjection := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  ext i j
  change ((leechCoordinateFrameVector 20 i : ℝ) / Real.sqrt 8) *
    ((leechCoordinateFrameVector 20 j : ℝ) / Real.sqrt 8) = _
  simp only [leechCoordinateFrameVector, Pi.single_apply,
    generatedEighthCoordinateLineProjection, Matrix.diagonal_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all

/-- Every actual isometry fixing this coordinate line belongs to the original monomial group. -/
theorem generatedEighth_coordinate_line_fixed_monomial (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g generatedEighthCoordinateLineProjection =
      generatedEighthCoordinateLineProjection) : g ∈ golayMonomialSubgroup := by
  obtain ⟨p, hp⟩ := leechSignedFrame_mem_monomial_orbit (20, 0)
  change p • leechNormEightAxis = leechSignedFrame (20, 0) at hp
  have hp' : conwayMatrixAction p.val (generatedNormEightLineMatrix leechNormEightAxis) =
      (8 : ℝ) • generatedEighthCoordinateLineProjection := by
    rw [← generatedNormEightLineMatrix_action]
    change generatedNormEightLineMatrix (p • leechNormEightAxis) = _
    rw [hp]
    exact generatedEighth_coordinate_frame_outer
  have he : conwayMatrixAction (p.val⁻¹ * g * p.val)
      (generatedNormEightLineMatrix leechNormEightAxis) =
        generatedNormEightLineMatrix leechNormEightAxis := by
    rw [map_mul, map_mul]
    change conwayMatrixAction p.val⁻¹
      (conwayMatrixAction g
        (conwayMatrixAction p.val (generatedNormEightLineMatrix leechNormEightAxis))) = _
    rw [hp', map_smul, hg, ← hp']
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hc : p.val⁻¹ * g * p.val ∈ golayMonomialSubgroup :=
    generatedNormEightLineStabilizer_le_monomial
      ((generatedNormEightLineStabilizer_mem _).mpr he)
  have hm := golayMonomialSubgroup.mul_mem
    (golayMonomialSubgroup.mul_mem p.property hc)
    (golayMonomialSubgroup.inv_mem p.property)
  have hprod : p.val * (p.val⁻¹ * g * p.val) * p.val⁻¹ = g := by group
  rwa [hprod] at hm

/-- Fixing the full actual matrix forces membership in the genuine Golay monomial subgroup. -/
theorem generatedEighth_matrix_fixed_monomial (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedEighthAxis).1 =
      (griessConwayEncode generatedEighthAxis).1) : g ∈ golayMonomialSubgroup :=
  generatedEighth_coordinate_line_fixed_monomial g
    ((generatedEighth_matrix_stabilizer_iff g).mp hg).2

/-- Every full-axis stabilizer fiber has an actual signed Golay permutation as spatial part. -/
theorem generatedEighth_full_fixed_spatial_monomial (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedEighthAxis = generatedEighthAxis) :
    f.val.2 ∈ golayMonomialSubgroup := by
  apply generatedEighth_matrix_fixed_monomial
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix] at hm
  exact hm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
