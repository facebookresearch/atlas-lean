/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ProjectionRecognition

/-! The actual fifth matrix recognizes its genuine coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The selected actual Golay word is the original literal octad2052. -/
theorem generatedFifth_flag_word_coordinate (i : Fin 24) :
    golayOctadWord generatedFifthFlagOctad i =
      golayBooleanCast (Nat.testBit 0x0f000f i.val) := by
  rw [golayOctadWord, golayLabelEncoder_boolean, generatedFifthFlagOctad_mask]

/-- The original fifth matrix is a quarter identity plus a quarter actual E8 projector. -/
theorem generatedFifth_matrix_affine_projection :
    (griessConwayEncode generatedFifthAxis).1 =
      (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
        (1 / 4 : ℝ) • Matrix.diagonal (fun i =>
          if golayOctadWord generatedFifthFlagOctad i = 0 then (0 : ℝ) else 1) := by
  rw [generatedFifth_matrix]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, generatedFifth_flag_word_coordinate]
  by_cases hij : i = j <;> cases h : Nat.testBit 0x0f000f j.val <;>
    norm_num [hij, h, golayBooleanCast]

/-- Fixing the actual fifth matrix is exactly preserving its actual integral E8 section. -/
theorem generatedFifth_matrix_stabilizer_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedFifthAxis).1 =
      (griessConwayEncode generatedFifthAxis).1 ↔
        generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad) =
          generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad) := by
  rw [generatedFifth_matrix_affine_projection, map_add, map_smul, map_smul,
    conwayMatrixAction_one, add_right_inj]
  rw [(smul_right_injective _ (by norm_num : (1 / 4 : ℝ) ≠ 0)).eq_iff]
  exact generatedAxisE8_matrix_action_iff_section_stabilizer _ g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
