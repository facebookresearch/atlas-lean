/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MovingSofa

/-!
# Actual moving-square and corridor boundary tests

These tests use canonical planar Lebesgue measure and the implemented continuous
motion. The corner points are deliberately not entrance or exit points.
-/

@[expose] public section

open MeasureTheory MovingSofa

namespace MathlibExtTest.Geometry.MovingSofa

theorem actual_square_passage : CanPass unitSquare := square_canPass

theorem actual_square_area : volume unitSquare = 1 := square_area

theorem actual_square_nonempty : unitSquare.Nonempty := square_connected.1

theorem actual_square_member : (1 : ℂ) ∈ unitSquare := by
  norm_num [unitSquare]

theorem actual_area_one_sofa : ∃ K : Set ℂ, IsSofa K ∧ volume K = 1 :=
  ⟨unitSquare, square_isSofa, square_area⟩

theorem actual_global_lower : 1 ≤ optimalArea := one_le_optimalArea

theorem actual_start_origin : squareMotion.position 0 0 = -1 := by
  norm_num [Motion.position, squareMotion]

theorem actual_end_origin : squareMotion.position 1 0 = Complex.I := by
  norm_num [Motion.position, squareMotion]

theorem actual_corner_time (z : ℂ) :
    squareMotion.position ⟨1 / 2, by norm_num⟩ z = z := by
  norm_num [Motion.position, squareMotion]

theorem actual_horizontal_arm : (-2 : ℂ) ∈ corridor := by
  norm_num [corridor]

theorem actual_vertical_arm : (2 : ℂ) * Complex.I ∈ corridor := by
  norm_num [corridor]

theorem actual_outside_corridor : (2 : ℂ) ∉ corridor := by
  norm_num [corridor]

theorem actual_corner_not_entrance : (1 / 2 : ℂ) ∉ entrance := by
  norm_num [entrance]

theorem actual_corner_not_exit : (1 / 2 : ℂ) ∉ exit := by
  norm_num [exit]

theorem actual_no_empty_sofa : ¬ IsSofa (∅ : Set ℂ) := by
  intro h
  rcases h.2.1 with ⟨⟨z, hz⟩, _⟩
  exact hz

theorem actual_square_passage_other : CanPassOther unitSquare :=
  square_canPassOther

theorem actual_square_ambidextrous : IsAmbidextrousSofa unitSquare :=
  square_isAmbidextrousSofa

theorem actual_ambidextrous_lower : 1 ≤ ambidextrousOptimalArea :=
  one_le_ambidextrousOptimalArea

theorem actual_ambidextrous_le_ordinary :
    ambidextrousOptimalArea ≤ optimalArea :=
  ambidextrousOptimalArea_le_optimalArea

theorem actual_other_start_origin : squareMotionOther.position 0 0 = 0 := by
  norm_num [Motion.position, squareMotionOther]

theorem actual_other_end_origin :
    squareMotionOther.position 1 0 = -1 + Complex.I := by
  norm_num [Motion.position, squareMotionOther]

theorem actual_other_corner_time (z : ℂ) :
    squareMotionOther.position ⟨1 / 2, by norm_num⟩ z = z - 1 := by
  norm_num [Motion.position, squareMotionOther, sub_eq_add_neg]

theorem actual_other_horizontal_arm : (2 : ℂ) ∈ corridorOther := by
  norm_num [corridorOther]

theorem actual_other_vertical_arm : (-1 + 2 * Complex.I : ℂ) ∈ corridorOther := by
  norm_num [corridorOther]

theorem actual_other_outside : (-2 : ℂ) ∉ corridorOther := by
  norm_num [corridorOther]


theorem actual_square_passage_z : CanPassZ unitSquare := square_canPassZ

theorem actual_z_start_origin : squareMotionZ.position 0 0 = -1 := by
  norm_num [Motion.position, squareMotionZ, squareMotionZAt]

theorem actual_z_end_origin :
    squareMotionZ.position 1 0 = 1 + 2 * Complex.I := by
  norm_num [Motion.position, squareMotionZ, squareMotionZAt]

theorem actual_z_first_transition (z : ℂ) :
    squareMotionZ.position ⟨1 / 3, by norm_num⟩ z = z := by
  norm_num [Motion.position, squareMotionZ, squareMotionZAt]

theorem actual_z_second_transition (z : ℂ) :
    squareMotionZ.position ⟨2 / 3, by norm_num⟩ z = z + 2 * Complex.I := by
  norm_num [Motion.position, squareMotionZ, squareMotionZAt]

theorem actual_z_entrance_arm : (-2 : ℂ) ∈ corridorZ 1 := by
  norm_num [corridorZ]

theorem actual_z_middle : (1 / 2 + 3 / 2 * Complex.I : ℂ) ∈ corridorZ 1 := by
  norm_num [corridorZ]

theorem actual_z_exit_arm : (2 + 5 / 2 * Complex.I : ℂ) ∈ corridorZ 1 := by
  norm_num [corridorZ]

theorem actual_z_bounded_above : (1 / 2 + 7 / 2 * Complex.I : ℂ) ∉ corridorZ 1 := by
  norm_num [corridorZ]

theorem actual_z_separation_matters :
    (1 / 2 + 5 / 2 * Complex.I : ℂ) ∉ corridorZ 0 ∧
      (1 / 2 + 5 / 2 * Complex.I : ℂ) ∈ corridorZ 1 := by
  constructor <;> norm_num [corridorZ]

end MathlibExtTest.Geometry.MovingSofa
