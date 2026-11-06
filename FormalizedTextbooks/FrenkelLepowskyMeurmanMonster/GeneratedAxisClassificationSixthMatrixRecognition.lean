/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMatrixPolynomial

/-! The original sixth-axis matrix recognizes an actual coordinate plane and genuine short line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- The 576 actual matrix entries have only rational coordinate and pair-sign arithmetic.
/-- The actual watermark is precisely the rooted-plane matrix with its genuine short outer. -/
theorem generatedSixth_axis_matrix_rooted_plane :
    (griessConwayEncode generatedSixthAxis).1 =
      generatedSixthRootedPlaneMatrix generatedSixthPlaneProjection generatedSixthPlaneOuter := by
  rw [generatedSixth_axis_matrix]
  ext i j
  have hu : generatedSixthPlaneOuter i j =
      ((generatedSixthPlaneRoot i : ℝ) * (generatedSixthPlaneRoot j : ℝ)) / 8 := by
    simp only [generatedSixthPlaneOuter, generatedAxisE8ShortOuter, Matrix.vecMulVec_apply,
      griessShortVector, generatedSixth_plane_root_actual]
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  simp only [generatedSixthRootedPlaneMatrix, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, generatedSixthPlaneProjection,
    Matrix.map_apply, Int.coe_castRingHom]
  rw [hu]
  fin_cases i <;> fin_cases j <;>
    norm_num [generatedSixthAxisMatrix, generatedSixthMiddlePairValue,
      generatedSixthPlaneNumerator, generatedSixthPlaneSupport, generatedSixthPlaneRoot]

/-- Fixing the original matrix is exactly fixing the actual rooted plane and its short label. -/
theorem generatedSixth_axis_matrix_fixed_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedSixthAxis).1 =
        (griessConwayEncode generatedSixthAxis).1 ↔
      conwayMatrixAction g generatedSixthPlaneProjection = generatedSixthPlaneProjection ∧
        griessShortPermutation g generatedSixthPlaneShort = generatedSixthPlaneShort := by
  rw [generatedSixth_axis_matrix_rooted_plane,
    generatedSixthRootedPlaneMatrix_fix_iff g _ _ generatedSixth_plane_projection_square
      generatedSixth_plane_outer_square generatedSixth_plane_projection_outer
      generatedSixth_plane_outer_projection]
  exact and_congr_right fun _ => generatedAxisE8ShortOuter_fix_iff g generatedSixthPlaneShort

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
