/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagRecognition

/-! An actual rank-two projection and its incident genuine Leech short root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The ordinary real orthogonal projection on the selected sum-zero coordinate plane. -/
def generatedSixthPlaneProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 3 : ℝ) • generatedSixthPlaneNumerator.map (Int.castRingHom ℝ)

/-- The rooted line is the genuine preferred minus pair on coordinates sixteen and seventeen. -/
def generatedSixthPlaneShort : GriessShortIndex := Sum.inl (0, generatedSixthTargetPair 0)

/-- The rooted line's genuine physical outer matrix. -/
def generatedSixthPlaneOuter : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedAxisE8ShortOuter generatedSixthPlaneShort

/-- The literal integer root is exactly the original preferred short vector. -/
theorem generatedSixth_plane_root_actual :
    griessShortIntegral generatedSixthPlaneShort = generatedSixthPlaneRoot := by
  ext i
  simp only [generatedSixthPlaneShort, griessShortIntegral,
    (generatedSixth_pair_coordinate_certificate 0).2, Matrix.cons_val_zero,
    ite_true, generatedSixthPlaneRoot]
  ring

/-- The actual real projection is idempotent. -/
theorem generatedSixth_plane_projection_square :
    generatedSixthPlaneProjection * generatedSixthPlaneProjection =
      generatedSixthPlaneProjection := by
  let N : Matrix (Fin 24) (Fin 24) ℝ :=
    generatedSixthPlaneNumerator.map (Int.castRingHom ℝ)
  have hn : N * N = (3 : ℝ) • N := by
    ext i j
    have hi := congrFun (congrFun generatedSixth_plane_numerator_square i) j
    change (∑ k, generatedSixthPlaneNumerator i k * generatedSixthPlaneNumerator k j) =
      3 * generatedSixthPlaneNumerator i j at hi
    change (∑ k, (generatedSixthPlaneNumerator i k : ℝ) *
      (generatedSixthPlaneNumerator k j : ℝ)) = 3 * (generatedSixthPlaneNumerator i j : ℝ)
    exact_mod_cast hi
  change ((1 / 3 : ℝ) • N) * ((1 / 3 : ℝ) • N) = (1 / 3 : ℝ) • N
  simp only [smul_mul_assoc, mul_smul_comm, hn, smul_smul]
  module

/-- The actual projection is symmetric. -/
theorem generatedSixth_plane_projection_symm :
    generatedSixthPlaneProjection.transpose = generatedSixthPlaneProjection := by
  ext i j
  have h := congrFun (congrFun generatedSixth_plane_numerator_symm i) j
  change generatedSixthPlaneNumerator j i = generatedSixthPlaneNumerator i j at h
  simp only [generatedSixthPlaneProjection, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul, h]

/-- The projection fixes the genuine physical short root. -/
theorem generatedSixth_plane_projection_root :
    generatedSixthPlaneProjection *ᵥ griessShortVector generatedSixthPlaneShort =
      griessShortVector generatedSixthPlaneShort := by
  ext i
  have h := congrFun generatedSixth_plane_numerator_root i
  change (∑ j, generatedSixthPlaneNumerator i j * generatedSixthPlaneRoot j) =
    3 * generatedSixthPlaneRoot i at h
  have hr : (∑ j, (generatedSixthPlaneNumerator i j : ℝ) *
      (generatedSixthPlaneRoot j : ℝ)) = 3 * (generatedSixthPlaneRoot i : ℝ) := by
    exact_mod_cast h
  simp only [Matrix.mulVec, dotProduct, generatedSixthPlaneProjection, Matrix.smul_apply,
    Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul, griessShortVector,
    generatedSixth_plane_root_actual]
  calc
    _ = (∑ j, (generatedSixthPlaneNumerator i j : ℝ) *
      (generatedSixthPlaneRoot j : ℝ)) / (3 * Real.sqrt 8) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (generatedSixthPlaneRoot i : ℝ) / Real.sqrt 8 := by rw [hr]; ring

/-- Squaring the actual short outer multiplies it by its authentic squared norm four. -/
theorem generatedSixth_plane_outer_square :
    generatedSixthPlaneOuter * generatedSixthPlaneOuter = (4 : ℝ) • generatedSixthPlaneOuter :=
  generatedAxisE8ShortOuter_square generatedSixthPlaneShort

/-- The rooted short outer is fixed on the left by the actual plane projection. -/
theorem generatedSixth_plane_projection_outer :
    generatedSixthPlaneProjection * generatedSixthPlaneOuter = generatedSixthPlaneOuter := by
  unfold generatedSixthPlaneOuter generatedAxisE8ShortOuter
  rw [Matrix.mul_vecMulVec, generatedSixth_plane_projection_root]

/-- The rooted short outer is also fixed on the right by the actual plane projection. -/
theorem generatedSixth_plane_outer_projection :
    generatedSixthPlaneOuter * generatedSixthPlaneProjection = generatedSixthPlaneOuter := by
  have h := congrArg Matrix.transpose generatedSixth_plane_projection_outer
  have hu : generatedSixthPlaneOuter.transpose = generatedSixthPlaneOuter := by
    ext i j
    simp only [generatedSixthPlaneOuter, generatedAxisE8ShortOuter, Matrix.transpose_apply,
      Matrix.vecMulVec_apply, mul_comm]
  simpa only [Matrix.transpose_mul, generatedSixth_plane_projection_symm, hu] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
