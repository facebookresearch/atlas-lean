/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! Binding the genuine odd-image matrix stabilizer to the actual norm-eight line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine distinguished norm-eight vector has outer matrix eight times its line projector. -/
theorem generatedNormEightLineMatrix_axis :
    generatedNormEightLineMatrix leechNormEightAxis =
      Matrix.diagonal (fun j : Fin 24 => if j = 0 then (8 : ℝ) else 0) := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  ext i j
  change ((leechCoordinateFrameVector 0 i : ℝ) / Real.sqrt 8) *
    ((leechCoordinateFrameVector 0 j : ℝ) / Real.sqrt 8) = _
  simp only [leechCoordinateFrameVector, Pi.single_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- The actual odd-image matrix is a fixed scalar matrix plus a quarter of the physical outer. -/
theorem generatedNormEightLine_odd_matrix (d : Fin 2048) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, 0))) c))).1 =
      (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
        (1 / 4 : ℝ) • generatedNormEightLineMatrix leechNormEightAxis := by
  rw [generatedAxis_triality_odd_matrix, generatedNormEightLineMatrix_axis]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- Fixing the actual odd-image matrix is exactly preserving its genuine norm-eight line. -/
theorem generatedNormEightLine_odd_stabilizer_iff (g : leechIsomSubgroup)
    (d : Fin 2048) (c : ZMod 2) :
    conwayMatrixAction g
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, 0))) c))).1 =
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, 0))) c))).1 ↔
        g ∈ generatedNormEightLineStabilizer := by
  rw [generatedNormEightLine_odd_matrix, map_add, map_smul, map_smul,
    conwayMatrixAction_one, generatedNormEightLineStabilizer_mem, add_right_inj]
  exact smul_right_injective _ (by norm_num : (1 / 4 : ℝ) ≠ 0) |>.eq_iff

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
