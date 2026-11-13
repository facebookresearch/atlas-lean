/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.AlexandrovGeometry.Euclidean

-- Tests for four-point comparison: half-plane witness and tightness controls.

open Real

namespace AlexandrovGeometry

/-- Closed half-plane is `Alex 0` by heredity from Euclidean space. -/
theorem halfplane_isAlex_zero :
    IsAlex 0 ↥{v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 1} := by
  have hbase : IsAlex 0 (EuclideanSpace ℝ (Fin 2)) :=
    isAlex_zero_of_innerProductSpace (V := EuclideanSpace ℝ (Fin 2))
  exact IsAlex.subtype hbase {v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 1}

/-- First line triple is defined for `κ = 0`. -/
theorem line_defined_12 : ModelAngleDefined 0 (0 : ℝ) 1 2 := by
  have hxy : dist (1 : ℝ) (2 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have hpx : dist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have hpy : dist (0 : ℝ) (2 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  unfold ModelAngleDefined ModelTriangleDefined
  rw [hxy, hpx, hpy]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by norm_num, by norm_num⟩
  intro h
  exact absurd h (lt_irrefl 0)

/-- Second line triple is defined for `κ = 0`. -/
theorem line_defined_2neg1 : ModelAngleDefined 0 (0 : ℝ) 2 (-1) := by
  have hxy : dist (2 : ℝ) (-1 : ℝ) = 3 := by
    rw [Real.dist_eq]
    norm_num
  have hpx : dist (0 : ℝ) (2 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  have hpy : dist (0 : ℝ) (-1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  unfold ModelAngleDefined ModelTriangleDefined
  rw [hxy, hpx, hpy]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by norm_num, by norm_num⟩
  intro h
  exact absurd h (lt_irrefl 0)

/-- Third line triple is defined for `κ = 0`. -/
theorem line_defined_neg11 : ModelAngleDefined 0 (0 : ℝ) (-1) 1 := by
  have hxy : dist (-1 : ℝ) (1 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  have hpx : dist (0 : ℝ) (-1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have hpy : dist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  unfold ModelAngleDefined ModelTriangleDefined
  rw [hxy, hpx, hpy]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by norm_num, by norm_num⟩
  intro h
  exact absurd h (lt_irrefl 0)

/-- First comparison angle on the line is `0`. -/
theorem line_angle_12 : comparisonAngle 0 (0 : ℝ) 1 2 = 0 := by
  have hxy : dist (1 : ℝ) (2 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have hpx : dist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have hpy : dist (0 : ℝ) (2 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  unfold comparisonAngle
  rw [modelAngle_zero_left]
  rw [hxy, hpx, hpy]
  have hfrac : ((1 : ℝ) ^ 2 + 2 ^ 2 - 1 ^ 2) / (2 * 1 * 2) = 1 := by
    norm_num
  rw [hfrac, Real.arccos_one]

/-- Second comparison angle on the line is `π`. -/
theorem line_angle_2neg1 : comparisonAngle 0 (0 : ℝ) 2 (-1) = π := by
  have hxy : dist (2 : ℝ) (-1 : ℝ) = 3 := by
    rw [Real.dist_eq]
    norm_num
  have hpx : dist (0 : ℝ) (2 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  have hpy : dist (0 : ℝ) (-1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  unfold comparisonAngle
  rw [modelAngle_zero_left]
  rw [hxy, hpx, hpy]
  have hfrac : ((2 : ℝ) ^ 2 + 1 ^ 2 - 3 ^ 2) / (2 * 2 * 1) = -1 := by
    norm_num
  rw [hfrac, Real.arccos_neg_one]

/-- Third comparison angle on the line is `π`. -/
theorem line_angle_neg11 : comparisonAngle 0 (0 : ℝ) (-1) 1 = π := by
  have hxy : dist (-1 : ℝ) (1 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  have hpx : dist (0 : ℝ) (-1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have hpy : dist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  unfold comparisonAngle
  rw [modelAngle_zero_left]
  rw [hxy, hpx, hpy]
  have hfrac : ((1 : ℝ) ^ 2 + 1 ^ 2 - 2 ^ 2) / (2 * 1 * 1) = -1 := by
    norm_num
  rw [hfrac, Real.arccos_neg_one]

/-- Line quadruple sums to exactly `2 * π`, so strict `<` would fail. -/
theorem line_sum_eq_two_pi :
    comparisonAngle 0 (0 : ℝ) 1 2 + comparisonAngle 0 (0 : ℝ) 2 (-1) +
        comparisonAngle 0 (0 : ℝ) (-1) 1 =
      2 * π := by
  rw [line_angle_12, line_angle_2neg1, line_angle_neg11]
  ring

/-- Product plane with sup metric is not `Alex 0` via the tripod. -/
theorem prod_not_alex_zero : ¬ IsAlex 0 (ℝ × ℝ) := by
  intro h
  have r01 : dist (0 : ℝ) (1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have r0neg1 : dist (0 : ℝ) (-1 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have r00 : dist (0 : ℝ) (0 : ℝ) = 0 := by
    rw [Real.dist_eq]
    norm_num
  have r1neg1 : dist (1 : ℝ) (-1 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  have r11 : dist (1 : ℝ) (1 : ℝ) = 0 := by
    rw [Real.dist_eq]
    norm_num
  have rneg10 : dist (-1 : ℝ) (0 : ℝ) = 1 := by
    rw [Real.dist_eq]
    norm_num
  have rneg11 : dist (-1 : ℝ) (1 : ℝ) = 2 := by
    rw [Real.dist_eq]
    norm_num
  have hp1 : dist ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) = 1 := by
    rw [Prod.dist_eq, r01]
    exact max_eq_left (le_refl (1 : ℝ))
  have hp2 : dist ((0, 0) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ) = 1 := by
    rw [Prod.dist_eq, r0neg1, r01]
    exact max_eq_left (le_refl (1 : ℝ))
  have hp3 : dist ((0, 0) : ℝ × ℝ) ((0, -1) : ℝ × ℝ) = 1 := by
    rw [Prod.dist_eq, r00, r0neg1]
    exact max_eq_right (by norm_num : (0 : ℝ) ≤ 1)
  have h12 : dist ((1, 1) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ) = 2 := by
    rw [Prod.dist_eq, r1neg1, r11]
    exact max_eq_left (by norm_num : (0 : ℝ) ≤ 2)
  have h23 : dist ((-1, 1) : ℝ × ℝ) ((0, -1) : ℝ × ℝ) = 2 := by
    rw [Prod.dist_eq, rneg10, r1neg1]
    exact max_eq_right (by norm_num : (1 : ℝ) ≤ 2)
  have h31 : dist ((0, -1) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) = 2 := by
    rw [Prod.dist_eq, r01, rneg11]
    exact max_eq_right (by norm_num : (1 : ℝ) ≤ 2)
  have hdef1 : ModelAngleDefined 0 ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ)
      ((-1, 1) : ℝ × ℝ) := by
    unfold ModelAngleDefined ModelTriangleDefined
    rw [h12, hp1, hp2]
    refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by norm_num, by norm_num⟩
    intro hcontra
    exact absurd hcontra (lt_irrefl 0)
  have hdef2 : ModelAngleDefined 0 ((0, 0) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ)
      ((0, -1) : ℝ × ℝ) := by
    unfold ModelAngleDefined ModelTriangleDefined
    rw [h23, hp2, hp3]
    refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by norm_num, by norm_num⟩
    intro hcontra
    exact absurd hcontra (lt_irrefl 0)
  have hdef3 : ModelAngleDefined 0 ((0, 0) : ℝ × ℝ) ((0, -1) : ℝ × ℝ)
      ((1, 1) : ℝ × ℝ) := by
    unfold ModelAngleDefined ModelTriangleDefined
    rw [h31, hp3, hp1]
    refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by norm_num, by norm_num⟩
    intro hcontra
    exact absurd hcontra (lt_irrefl 0)
  have c1 : comparisonAngle 0 ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ)
      ((-1, 1) : ℝ × ℝ) = π := by
    unfold comparisonAngle
    rw [modelAngle_zero_left]
    rw [h12, hp1, hp2]
    have hfrac : ((1 : ℝ) ^ 2 + 1 ^ 2 - 2 ^ 2) / (2 * 1 * 1) = -1 := by
      norm_num
    rw [hfrac, Real.arccos_neg_one]
  have c2 : comparisonAngle 0 ((0, 0) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ)
      ((0, -1) : ℝ × ℝ) = π := by
    unfold comparisonAngle
    rw [modelAngle_zero_left]
    rw [h23, hp2, hp3]
    have hfrac : ((1 : ℝ) ^ 2 + 1 ^ 2 - 2 ^ 2) / (2 * 1 * 1) = -1 := by
      norm_num
    rw [hfrac, Real.arccos_neg_one]
  have c3 : comparisonAngle 0 ((0, 0) : ℝ × ℝ) ((0, -1) : ℝ × ℝ)
      ((1, 1) : ℝ × ℝ) = π := by
    unfold comparisonAngle
    rw [modelAngle_zero_left]
    rw [h31, hp3, hp1]
    have hfrac : ((1 : ℝ) ^ 2 + 1 ^ 2 - 2 ^ 2) / (2 * 1 * 1) = -1 := by
      norm_num
    rw [hfrac, Real.arccos_neg_one]
  have hle : comparisonAngle 0 ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ) +
      comparisonAngle 0 ((0, 0) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ) ((0, -1) : ℝ × ℝ) +
      comparisonAngle 0 ((0, 0) : ℝ × ℝ) ((0, -1) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) ≤ 2 * π :=
    h ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) ((-1, 1) : ℝ × ℝ)
      ((0, -1) : ℝ × ℝ) ⟨hdef1, hdef2, hdef3⟩
  rw [c1, c2, c3] at hle
  have hpi : 0 < π := Real.pi_pos
  linarith

/-- Edge is Alex 0; conjecture is about length metric, trivial for every restricted subset. -/
theorem edge_isAlex_zero :
    IsAlex 0 ↥{v : EuclideanSpace ℝ (Fin 2) | v 1 = 0} := by
  have hbase : IsAlex 0 (EuclideanSpace ℝ (Fin 2)) :=
    isAlex_zero_of_innerProductSpace (V := EuclideanSpace ℝ (Fin 2))
  exact IsAlex.subtype hbase {v : EuclideanSpace ℝ (Fin 2) | v 1 = 0}

/-- Frontier of univ is empty; Alex boundary is the edge line instead. -/
theorem frontier_halfplane_univ :
    frontier (Set.univ : Set ↥{v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 1}) = ∅ :=
  frontier_univ

end AlexandrovGeometry
