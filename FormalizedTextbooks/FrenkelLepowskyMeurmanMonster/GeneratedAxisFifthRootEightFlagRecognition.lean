/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisIntegralLineGeometry

/-! Recognize the complete original root-8 matrix by two actual integral lattice lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The lower distinguished line is the original norm 4 lattice line. -/
theorem generatedFifthRootEight_low_projection_line :
    generatedFifthRootEightLowProjection =
      (1 / 4 : ℝ) • generatedIntegralLineMatrix generatedFifthRootEightNormFour := by
  ext i j
  rw [Matrix.smul_apply, generatedIntegralLineMatrix_four_coordinates
    generatedFifthRootEightNormFour generatedFifthRootEightLowDirection (fun _ => rfl)]
  simp only [generatedFifthRootEightLowProjection, generatedFifthRootEightLowProjectionInteger,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  change (1 / 2 : ℝ) * ((generatedFifthRootEightLowDirection i *
      generatedFifthRootEightLowDirection j : ℤ) : ℝ) = _
  push_cast
  ring

/-- The higher distinguished line is twice the norm 6 vector minus the norm 4 vector. -/
theorem generatedFifthRootEight_high_projection_line :
    generatedFifthRootEightHighProjection =
      (1 / 20 : ℝ) • generatedIntegralLineMatrix generatedFifthRootEightNormTwenty := by
  ext i j
  rw [Matrix.smul_apply, generatedIntegralLineMatrix_four_coordinates
    generatedFifthRootEightNormTwenty generatedFifthRootEightHighDirection
      generatedFifthRootEight_norm_twenty_coordinates]
  simp only [generatedFifthRootEightHighProjection, generatedFifthRootEightHighProjectionInteger,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  change (1 / 10 : ℝ) * ((generatedFifthRootEightHighDirection i *
      generatedFifthRootEightHighDirection j : ℤ) : ℝ) = _
  push_cast
  ring

private theorem norm_four_ne_zero : generatedFifthRootEightNormFour ≠ 0 := by
  intro h
  have hs := generatedFifthRootEight_flag_integer_norms.1
  change leechSquareSum generatedFifthRootEightNormFour.val = 32 at hs
  rw [h] at hs
  norm_num [leechSquareSum] at hs

private theorem norm_twenty_ne_zero : generatedFifthRootEightNormTwenty ≠ 0 := by
  intro h
  have hs := generatedFifthRootEight_norm_twenty_square_sum
  rw [h] at hs
  norm_num [leechSquareSum] at hs

/-- The complete actual matrix fixes precisely the two genuine lattice lines, including signs. -/
theorem generatedFifthRootEight_matrix_fix_integral_lines_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedFifthRootEightAxis).1 =
      (griessConwayEncode generatedFifthRootEightAxis).1 ↔
      (leechIntegralAction g generatedFifthRootEightNormTwenty = generatedFifthRootEightNormTwenty ∨
        leechIntegralAction g generatedFifthRootEightNormTwenty =
          -generatedFifthRootEightNormTwenty) ∧
      (leechIntegralAction g generatedFifthRootEightNormFour = generatedFifthRootEightNormFour ∨
        leechIntegralAction g generatedFifthRootEightNormFour =
          -generatedFifthRootEightNormFour) := by
  rw [generatedFifthRootEight_matrix_fix_flag_iff,
    generatedFifthRootEight_high_projection_line, generatedFifthRootEight_low_projection_line]
  rw [generatedIntegralLineMatrix_smul_fix_iff g _ norm_twenty_ne_zero _ (by norm_num),
    generatedIntegralLineMatrix_smul_fix_iff g _ norm_four_ne_zero _ (by norm_num)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
