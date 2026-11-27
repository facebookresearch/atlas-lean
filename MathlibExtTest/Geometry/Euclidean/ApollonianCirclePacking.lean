/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.ApollonianCirclePacking

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Apollonian circle packings

The bounding circle of radius `6` centered at `0`, the two circles of radius `3` centered at
`±3` and the circle of radius `2` centered at `4i` form a Descartes configuration (signed
curvatures `(-1, 2, 2, 3) / 6`) whose first circle encloses the other three. This is a
non-degenerate instance of the hypotheses of the wanted Kontorovich–Oh counting theorem
(`WantedExt.Geometry.ApollonianCirclePackingWanted`).
-/

namespace MathlibExtTest.Geometry.Euclidean.ApollonianCirclePacking

open Complex MathlibExt.Geometry.Euclidean.ApollonianCirclePacking

/-- The circles of the test configuration. -/
noncomputable def C : Fin 4 → PlaneCircle :=
  ![{ center := 0, radius := 6, radius_pos := by norm_num },
    { center := 3, radius := 3, radius_pos := by norm_num },
    { center := -3, radius := 3, radius_pos := by norm_num },
    { center := 4 * I, radius := 2, radius_pos := by norm_num }]

/-- The six tangency points of the test configuration. -/
noncomputable def p : Fin 4 → Fin 4 → ℂ :=
  ![![0, 6, -6, 6 * I], ![6, 0, 0, 6 / 5 + 12 / 5 * I], ![-6, 0, 0, -6 / 5 + 12 / 5 * I],
    ![6 * I, 6 / 5 + 12 / 5 * I, -6 / 5 + 12 / 5 * I, 0]]

theorem norm_eq_of_normSq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : normSq z = r ^ 2) : ‖z‖ = r := by
  have h2 : ‖z‖ ^ 2 = r ^ 2 := by rw [Complex.sq_norm, h]
  exact (pow_left_inj₀ (norm_nonneg z) hr two_ne_zero).1 h2

theorem dist_C (i j : Fin 4) {r : ℝ} (hr : 0 ≤ r)
    (h : normSq ((C i).center - (C j).center) = r ^ 2) :
    dist (C i).center (C j).center = r := by
  rw [dist_eq_norm]
  exact norm_eq_of_normSq hr h

theorem tangent_01 : TangentAt (C 0) (C 1) (p 0 1) := by
  have hd : dist (C 0).center (C 1).center = (C 0).radius - (C 1).radius := by
    refine dist_C 0 1 (by norm_num [C]) ?_
    simp [C, normSq_apply]; norm_num
  have h := tangentAt_of_dist_eq_sub (C 0) (C 1) (by norm_num [C]) hd
  convert h using 1
  apply Complex.ext <;> simp [C, p, AffineMap.lineMap_apply] <;> norm_num

theorem tangent_02 : TangentAt (C 0) (C 2) (p 0 2) := by
  have hd : dist (C 0).center (C 2).center = (C 0).radius - (C 2).radius := by
    refine dist_C 0 2 (by norm_num [C]) ?_
    simp [C]; norm_num
  have h := tangentAt_of_dist_eq_sub (C 0) (C 2) (by norm_num [C]) hd
  convert h using 1
  apply Complex.ext <;> simp [C, p, AffineMap.lineMap_apply] <;> norm_num

theorem tangent_03 : TangentAt (C 0) (C 3) (p 0 3) := by
  have hd : dist (C 0).center (C 3).center = (C 0).radius - (C 3).radius := by
    refine dist_C 0 3 (by norm_num [C]) ?_
    simp [C, normSq_apply]; norm_num
  have h := tangentAt_of_dist_eq_sub (C 0) (C 3) (by norm_num [C]) hd
  convert h using 1
  apply Complex.ext <;> simp [C, p, AffineMap.lineMap_apply] <;> norm_num

theorem tangent_12 : TangentAt (C 1) (C 2) (p 1 2) := by
  have hd : dist (C 1).center (C 2).center = (C 1).radius + (C 2).radius := by
    refine dist_C 1 2 (by norm_num [C]) ?_
    simp [C, normSq_apply]; norm_num
  have h := tangentAt_of_dist_eq_add (C 1) (C 2) hd
  convert h using 1
  apply Complex.ext <;> simp [C, p, AffineMap.lineMap_apply] <;> norm_num

theorem tangent_13 : TangentAt (C 1) (C 3) (p 1 3) := by
  have hd : dist (C 1).center (C 3).center = (C 1).radius + (C 3).radius := by
    refine dist_C 1 3 (by norm_num [C]) ?_
    simp [C, normSq_apply]; norm_num
  have h := tangentAt_of_dist_eq_add (C 1) (C 3) hd
  convert h using 1
  apply Complex.ext <;> simp [C, p, AffineMap.lineMap_apply] <;> norm_num

theorem tangent_23 : TangentAt (C 2) (C 3) (p 2 3) := by
  have hd : dist (C 2).center (C 3).center = (C 2).radius + (C 3).radius := by
    refine dist_C 2 3 (by norm_num [C]) ?_
    simp [C, normSq_apply]; norm_num
  have h := tangentAt_of_dist_eq_add (C 2) (C 3) hd
  convert h using 1
  apply Complex.ext <;> simp [C, p, AffineMap.lineMap_apply] <;> norm_num

/-- The test configuration is a Descartes configuration. -/
theorem isDescartesConfiguration_C : IsDescartesConfiguration C := by
  refine ⟨?_, p, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [C, PlaneCircle.mk.injEq, Complex.ext_iff] <;> norm_num at hij
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact tangent_01
    · exact tangent_02
    · exact tangent_03
    · exact tangent_01.symm
    · exact tangent_12
    · exact tangent_13
    · exact tangent_02.symm
    · exact tangent_12.symm
    · exact tangent_23
    · exact tangent_03.symm
    · exact tangent_13.symm
    · exact tangent_23.symm
  · intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk <;>
      simp [p, Complex.ext_iff] <;> norm_num

/-- The first circle encloses the other three (internal tangency), as in the hypotheses of the
wanted Kontorovich–Oh counting theorem. -/
theorem bounding_C :
    ∀ j, j ≠ 0 → dist (C 0).center (C j).center = (C 0).radius - (C j).radius := by
  intro j hj
  fin_cases j
  · simp at hj
  all_goals
    refine dist_C _ _ (by norm_num [C]) ?_
    simp [C, normSq_apply]; norm_num

/-- The initial circles belong to the packing. -/
example : C 3 ∈ apollonianPacking C := mem_apollonianPacking C 3

end MathlibExtTest.Geometry.Euclidean.ApollonianCirclePacking
