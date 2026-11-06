/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthFlagData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthFlagMatrix

/-! The actual matrix recognizes its genuine dodecad projection and coordinate line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original eighth matrix is precisely the actual coordinate flag matrix. -/
theorem generatedEighth_matrix_coordinate_flag :
    (griessConwayEncode generatedEighthAxis).1 =
      generatedEighthCoordinateFlagMatrix generatedEighthDodecadProjection
        generatedEighthCoordinateLineProjection := by
  rw [generatedEighth_axis_matrix]
  have hbits : ∀ i : Fin 24, Nat.testBit 0xc5066f i.val = true ↔
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨
        i = 9 ∨ i = 10 ∨ i = 16 ∨ i = 18 ∨ i = 22 ∨ i = 23 := by
    decide +kernel
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 20
    · subst i
      have h20 : Nat.testBit 0xc5066f 20 = false := by decide
      norm_num [generatedEighthAxisMatrix, generatedEighthCoordinateFlagMatrix,
        generatedEighthDodecadProjection, generatedEighthCoordinateLineProjection, h20]
    · cases h : Nat.testBit 0xc5066f i.val
      · have hn := (hbits i).not.mp (by simp [h])
        simp [generatedEighthAxisMatrix, generatedEighthCoordinateFlagMatrix,
          generatedEighthDodecadProjection, generatedEighthCoordinateLineProjection, hi, h, hn]
      · have hp := (hbits i).mp h
        norm_num [generatedEighthAxisMatrix, generatedEighthCoordinateFlagMatrix,
          generatedEighthDodecadProjection, generatedEighthCoordinateLineProjection, hi, h, hp]
  · simp [generatedEighthAxisMatrix, generatedEighthCoordinateFlagMatrix,
      generatedEighthDodecadProjection, generatedEighthCoordinateLineProjection, hij]

/-- Full matrix fixation is exactly fixation of both genuine orthogonal projections. -/
theorem generatedEighth_matrix_stabilizer_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedEighthAxis).1 =
        (griessConwayEncode generatedEighthAxis).1 ↔
      conwayMatrixAction g generatedEighthDodecadProjection = generatedEighthDodecadProjection ∧
        conwayMatrixAction g generatedEighthCoordinateLineProjection =
          generatedEighthCoordinateLineProjection := by
  rw [generatedEighth_matrix_coordinate_flag]
  exact generatedEighthCoordinateFlagMatrix_fix_iff g _ _
    generatedEighth_dodecad_projection_square generatedEighth_coordinate_line_projection_square
    generatedEighth_dodecad_coordinate_line_mul.1 generatedEighth_dodecad_coordinate_line_mul.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
