/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.AlexandrovGeometry.FourPointComparison
import Mathlib.Analysis.SpecialFunctions.Arcosh

/- Tests for model angles: right angles, equilateral monotonicity, radius,
and degenerate vertex. -/

open Real

namespace AlexandrovGeometry

/-- `arccos (1 / 2)` equals `π / 3`. -/
theorem test_aux_arccos_half : Real.arccos (1 / 2 : ℝ) = π / 3 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h0 : (0 : ℝ) ≤ π / 3 := by linarith [hpi]
  have hle : π / 3 ≤ π := by linarith [hpi]
  have hcos : Real.cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
  rw [← hcos]
  exact Real.arccos_cos h0 hle

/-- Euclidean 3-4-5 triangle has right angle. -/
theorem test_euclid_345 : modelAngle 0 5 3 4 = π / 2 := by
  rw [modelAngle_zero_left]
  have hratio : ((3 : ℝ) ^ 2 + 4 ^ 2 - 5 ^ 2) / (2 * 3 * 4) = 0 := by
    norm_num
  rw [hratio]
  exact Real.arccos_zero

/-- Octant triangle is defined for `κ = 1`. -/
theorem test_octant_defined :
    ModelTriangleDefined 1 (π / 2) (π / 2) (π / 2) := by
  unfold ModelTriangleDefined
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : (0 : ℝ) ≤ π / 2 := le_of_lt Real.pi_div_two_pos
    linarith [hle]
  · have hle : (0 : ℝ) ≤ π / 2 := le_of_lt Real.pi_div_two_pos
    linarith [hle]
  · have hle : (0 : ℝ) ≤ π / 2 := le_of_lt Real.pi_div_two_pos
    linarith [hle]
  · intro _
    have hpi : (0 : ℝ) < π := Real.pi_pos
    have hsqrt : √(1 : ℝ) = 1 := Real.sqrt_one
    rw [hsqrt, div_one]
    linarith [hpi]

/-- Octant triangle has right angle. -/
theorem test_octant_angle :
    modelAngle 1 (π / 2) (π / 2) (π / 2) = π / 2 := by
  have h1ne : (1 : ℝ) ≠ 0 := one_ne_zero
  have hpos : (0 : ℝ) < 1 := zero_lt_one
  have hsqrt : √(1 : ℝ) = 1 := Real.sqrt_one
  have hcos : modelCos 1 (π / 2) = 0 := by
    rw [modelCos_of_pos hpos, hsqrt, one_mul, Real.cos_pi_div_two]
  have hsin : modelSin 1 (π / 2) = 1 := by
    rw [modelSin_of_pos hpos, hsqrt, one_mul, Real.sin_pi_div_two,
      div_one]
  rw [modelAngle_of_ne_zero h1ne, hcos, hsin]
  have hratio : ((0 : ℝ) - 0 * 0) / (1 * 1 * 1) = 0 := by norm_num
  rw [hratio]
  exact Real.arccos_zero

/-- Hyperbolic right triangle from `cosh` doubling. -/
theorem test_hyperbolic_right :
    modelAngle (-1) (Real.arcosh 4) (Real.arcosh 2) (Real.arcosh 2) =
      π / 2 := by
  have hneg : ¬ (0 : ℝ) < -1 := by norm_num
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  have hsqrt : √(-(-1 : ℝ)) = 1 := by
    simp only [neg_neg, Real.sqrt_one]
  have hcos4 : modelCos (-1) (Real.arcosh 4) = 4 := by
    rw [modelCos_of_neg (by norm_num : (-1 : ℝ) < 0), hsqrt, one_mul]
    exact Real.cosh_arcosh (by norm_num)
  have hcos2 : modelCos (-1) (Real.arcosh 2) = 2 := by
    rw [modelCos_of_neg (by norm_num : (-1 : ℝ) < 0), hsqrt, one_mul]
    exact Real.cosh_arcosh (by norm_num)
  rw [modelAngle_of_ne_zero hne, hcos4, hcos2]
  have hnum : (4 : ℝ) - 2 * 2 = 0 := by norm_num
  have hratio :
      ((4 : ℝ) - 2 * 2) /
        (-1 * modelSin (-1) (Real.arcosh 2) *
          modelSin (-1) (Real.arcosh 2)) = 0 := by
    rw [hnum]
    exact zero_div _
  rw [hratio]
  exact Real.arccos_zero

/-- Unit equilateral has angle `π / 3` for `κ = 0`. -/
theorem test_equilateral_zero : modelAngle 0 1 1 1 = π / 3 := by
  rw [modelAngle_zero_left]
  have hratio :
      ((1 : ℝ) ^ 2 + 1 ^ 2 - 1 ^ 2) / (2 * 1 * 1) = 1 / 2 := by
    norm_num
  rw [hratio]
  exact test_aux_arccos_half

/-- Unit equilateral has angle above `π / 3` for `κ = 1`. -/
theorem test_equilateral_pos : π / 3 < modelAngle 1 1 1 1 := by
  have hcos_pos : (0 : ℝ) < Real.cos 1 := Real.cos_one_pos
  have hcos_lt_one : Real.cos 1 < 1 := by
    have hle := Real.cos_one_le
    linarith [hle]
  have hsqrt1 : √(1 : ℝ) = 1 := Real.sqrt_one
  have hpos1 : (0 : ℝ) < 1 := zero_lt_one
  have h1ne : (1 : ℝ) ≠ 0 := one_ne_zero
  have hcos_eq : modelCos 1 1 = Real.cos 1 := by
    rw [modelCos_of_pos hpos1, hsqrt1, one_mul]
  have hsin_eq : modelSin 1 1 = Real.sin 1 := by
    rw [modelSin_of_pos hpos1, hsqrt1, one_mul, div_one]
  have htrig : Real.sin 1 ^ 2 + Real.cos 1 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq 1
  have hsin_sq : Real.sin 1 ^ 2 = 1 - Real.cos 1 ^ 2 := by
    linarith [htrig]
  have hc_sub_pos : (0 : ℝ) < 1 - Real.cos 1 := by
    linarith [hcos_lt_one]
  have hc_add_pos : (0 : ℝ) < 1 + Real.cos 1 := by
    linarith [hcos_pos]
  have hden_eq : (1 : ℝ) * Real.sin 1 * Real.sin 1 =
      Real.sin 1 ^ 2 := by ring
  have hc_add_ne : Real.cos 1 + 1 ≠ 0 := by
    apply ne_of_gt
    linarith [hcos_pos]
  have hc1_add_ne : (1 : ℝ) + Real.cos 1 ≠ 0 :=
    ne_of_gt hc_add_pos
  have hc_sub_ne : (1 : ℝ) - Real.cos 1 ≠ 0 :=
    ne_of_gt hc_sub_pos
  have hden2_ne : (1 : ℝ) - Real.cos 1 ^ 2 ≠ 0 := by
    have hfac : (1 : ℝ) - Real.cos 1 ^ 2 =
        (1 - Real.cos 1) * (1 + Real.cos 1) := by ring
    rw [hfac]
    exact mul_ne_zero hc_sub_ne hc1_add_ne
  have hval_eq :
      (Real.cos 1 - Real.cos 1 * Real.cos 1) /
        (1 * Real.sin 1 * Real.sin 1) =
        Real.cos 1 / (Real.cos 1 + 1) := by
    rw [hden_eq, hsin_sq]
    rw [div_eq_div_iff hden2_ne hc_add_ne]
    ring
  have hAngle_eq : modelAngle 1 1 1 1 =
      Real.arccos ((Real.cos 1 - Real.cos 1 * Real.cos 1) /
        (1 * Real.sin 1 * Real.sin 1)) := by
    rw [modelAngle_of_ne_zero h1ne, hcos_eq, hsin_eq]
  have hAngle_eq2 : modelAngle 1 1 1 1 =
      Real.arccos (Real.cos 1 / (Real.cos 1 + 1)) := by
    rw [hAngle_eq, hval_eq]
  have hval_lt : Real.cos 1 / (Real.cos 1 + 1) < 1 / 2 := by
    field_simp [hc_add_ne]
    linarith [hcos_lt_one]
  have hval_pos : (0 : ℝ) < Real.cos 1 / (Real.cos 1 + 1) := by
    apply div_pos hcos_pos
    linarith [hcos_pos]
  have hlower : (-1 : ℝ) ≤ Real.cos 1 / (Real.cos 1 + 1) := by
    linarith [hval_pos]
  have hupper : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rw [hAngle_eq2, ← test_aux_arccos_half]
  exact Real.arccos_lt_arccos hlower hval_lt hupper

/-- Unit equilateral has angle below `π / 3` for `κ = -1`. -/
theorem test_equilateral_neg : modelAngle (-1) 1 1 1 < π / 3 := by
  have hcosh_gt : (1 : ℝ) < Real.cosh 1 :=
    Real.one_lt_cosh.mpr one_ne_zero
  have hcosh_pos : (0 : ℝ) < Real.cosh 1 := Real.cosh_pos 1
  have hneg : ¬ (0 : ℝ) < -1 := by norm_num
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  have hsqrt : √(-(-1 : ℝ)) = 1 := by
    simp only [neg_neg, Real.sqrt_one]
  have hcos_eq : modelCos (-1) 1 = Real.cosh 1 := by
    rw [modelCos_of_neg (by norm_num : (-1 : ℝ) < 0), hsqrt, one_mul]
  have hsin_eq : modelSin (-1) 1 = Real.sinh 1 := by
    rw [modelSin_of_neg (by norm_num : (-1 : ℝ) < 0), hsqrt, one_mul,
      div_one]
  have hcosh_sq : Real.cosh 1 ^ 2 = Real.sinh 1 ^ 2 + 1 :=
    Real.cosh_sq 1
  have hsinh_sq : Real.sinh 1 ^ 2 = Real.cosh 1 ^ 2 - 1 := by
    linarith [hcosh_sq]
  have hden_eq : (-1 : ℝ) * Real.sinh 1 * Real.sinh 1 =
      -(Real.sinh 1 ^ 2) := by ring
  have hadd_ne : Real.cosh 1 + 1 ≠ 0 := by
    apply ne_of_gt
    linarith [hcosh_pos]
  have hsub_ne : Real.cosh 1 - 1 ≠ 0 := by
    apply ne_of_gt
    linarith [hcosh_gt]
  have hden2_ne : -(Real.cosh 1 ^ 2 - 1) ≠ 0 := by
    have hfac : Real.cosh 1 ^ 2 - 1 =
        (Real.cosh 1 - 1) * (Real.cosh 1 + 1) := by ring
    rw [hfac]
    exact neg_ne_zero.mpr (mul_ne_zero hsub_ne hadd_ne)
  have hval_eq :
      (Real.cosh 1 - Real.cosh 1 * Real.cosh 1) /
        (-1 * Real.sinh 1 * Real.sinh 1) =
        Real.cosh 1 / (Real.cosh 1 + 1) := by
    rw [hden_eq, hsinh_sq]
    rw [div_eq_div_iff hden2_ne hadd_ne]
    ring
  have hAngle_eq : modelAngle (-1) 1 1 1 =
      Real.arccos ((Real.cosh 1 - Real.cosh 1 * Real.cosh 1) /
        (-1 * Real.sinh 1 * Real.sinh 1)) := by
    rw [modelAngle_of_ne_zero hne, hcos_eq, hsin_eq]
  have hAngle_eq2 : modelAngle (-1) 1 1 1 =
      Real.arccos (Real.cosh 1 / (Real.cosh 1 + 1)) := by
    rw [hAngle_eq, hval_eq]
  have hval_gt : (1 / 2 : ℝ) < Real.cosh 1 / (Real.cosh 1 + 1) := by
    field_simp [hadd_ne]
    linarith [hcosh_gt]
  have hval_lt_one : Real.cosh 1 / (Real.cosh 1 + 1) < 1 := by
    field_simp [hadd_ne]
    linarith [hcosh_pos]
  have hlower : (-1 : ℝ) ≤ 1 / 2 := by norm_num
  have hupper : Real.cosh 1 / (Real.cosh 1 + 1) ≤ 1 :=
    le_of_lt hval_lt_one
  rw [hAngle_eq2, ← test_aux_arccos_half]
  exact Real.arccos_lt_arccos hlower hval_gt hupper

/-- Perimeter `2 * π` is not allowed for `κ = 1`. -/
theorem test_radius : ¬ ModelTriangleDefined 1 π (π / 2) (π / 2) := by
  intro h
  unfold ModelTriangleDefined at h
  have hper := h.2.2.2 zero_lt_one
  have hsqrt : √(1 : ℝ) = 1 := Real.sqrt_one
  rw [hsqrt, div_one] at hper
  have hsum : π + π / 2 + π / 2 = 2 * π := by ring
  rw [hsum] at hper
  exact lt_irrefl _ hper

/-- Zero side at `p` makes the angle undefined. -/
theorem test_degenerate (κ : ℝ) :
    ¬ ModelAngleDefined κ (0 : ℝ) 0 1 := by
  intro h
  unfold ModelAngleDefined at h
  have hpos := h.2.1
  have hzero : dist (0 : ℝ) (0 : ℝ) = 0 := dist_self 0
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- Spherical cosine law at `κ = 1`. -/
theorem test_spherical_law (a b c : ℝ) :
    modelAngle 1 a b c = Real.arccos ((Real.cos a - Real.cos b * Real.cos c) /
      (Real.sin b * Real.sin c)) := by
  have h1ne : (1 : ℝ) ≠ 0 := one_ne_zero
  have hpos : (0 : ℝ) < 1 := zero_lt_one
  have hsqrt : √(1 : ℝ) = 1 := Real.sqrt_one
  have hcos_a : modelCos 1 a = Real.cos a := by
    rw [modelCos_of_pos hpos, hsqrt, one_mul]
  have hcos_b : modelCos 1 b = Real.cos b := by
    rw [modelCos_of_pos hpos, hsqrt, one_mul]
  have hcos_c : modelCos 1 c = Real.cos c := by
    rw [modelCos_of_pos hpos, hsqrt, one_mul]
  have hsin_b : modelSin 1 b = Real.sin b := by
    rw [modelSin_of_pos hpos, hsqrt, one_mul, div_one]
  have hsin_c : modelSin 1 c = Real.sin c := by
    rw [modelSin_of_pos hpos, hsqrt, one_mul, div_one]
  rw [modelAngle_of_ne_zero h1ne, hcos_a, hcos_b, hcos_c, hsin_b, hsin_c,
    one_mul]

/-- Hyperbolic cosine law at `κ = -1`. -/
theorem test_hyperbolic_law (a b c : ℝ) :
    modelAngle (-1) a b c =
      Real.arccos ((Real.cosh a - Real.cosh b * Real.cosh c) /
        (-(Real.sinh b * Real.sinh c))) := by
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  have hneg : (-1 : ℝ) < 0 := by norm_num
  have hsqrt : √(-(-1 : ℝ)) = 1 := by
    simp only [neg_neg, Real.sqrt_one]
  have hcos_a : modelCos (-1) a = Real.cosh a := by
    rw [modelCos_of_neg hneg, hsqrt, one_mul]
  have hcos_b : modelCos (-1) b = Real.cosh b := by
    rw [modelCos_of_neg hneg, hsqrt, one_mul]
  have hcos_c : modelCos (-1) c = Real.cosh c := by
    rw [modelCos_of_neg hneg, hsqrt, one_mul]
  have hsin_b : modelSin (-1) b = Real.sinh b := by
    rw [modelSin_of_neg hneg, hsqrt, one_mul, div_one]
  have hsin_c : modelSin (-1) c = Real.sinh c := by
    rw [modelSin_of_neg hneg, hsqrt, one_mul, div_one]
  have hden : (-1 : ℝ) * Real.sinh b * Real.sinh c =
      -(Real.sinh b * Real.sinh c) := by ring
  rw [modelAngle_of_ne_zero hne, hcos_a, hcos_b, hcos_c, hsin_b, hsin_c,
    hden]

/-- Octant angle is not given by the Euclidean formula. -/
theorem test_octant_not_euclid :
    modelAngle 1 (π / 2) (π / 2) (π / 2) ≠
      Real.arccos (((π / 2) ^ 2 + (π / 2) ^ 2 - (π / 2) ^ 2) /
        (2 * (π / 2) * (π / 2))) := by
  rw [test_octant_angle]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hne : (π / 2 : ℝ) ≠ 0 := ne_of_gt (by linarith [hpi])
  have hratio : (((π / 2 : ℝ) ^ 2 + (π / 2) ^ 2 - (π / 2) ^ 2) /
      (2 * (π / 2) * (π / 2)) = 1 / 2) := by
    field_simp [hne]
    ring
  rw [hratio, test_aux_arccos_half]
  have hlt : π / 3 < π / 2 := by linarith [hpi]
  exact ne_of_gt hlt

/-- The `κ ≠ 0` formula fails at `κ = 0`. -/
theorem test_zero_not_ne_zero :
    modelAngle 0 3 4 5 ≠
      Real.arccos ((modelCos 0 3 - modelCos 0 4 * modelCos 0 5) /
        (0 * modelSin 0 4 * modelSin 0 5)) := by
  rw [modelAngle_zero_left]
  have hden : (0 : ℝ) * modelSin 0 4 * modelSin 0 5 = 0 := by
    simp only [zero_mul]
  have hrhs : (modelCos 0 3 - modelCos 0 4 * modelCos 0 5) /
      (0 * modelSin 0 4 * modelSin 0 5) = 0 := by
    rw [hden]
    exact div_zero _
  rw [hrhs, Real.arccos_zero]
  have hratio : ((4 : ℝ) ^ 2 + 5 ^ 2 - 3 ^ 2) / (2 * 4 * 5) = 32 / 40 := by
    norm_num
  rw [hratio]
  intro hcontra
  have hx : (32 / 40 : ℝ) = 0 := Real.arccos_eq_pi_div_two.mp hcontra
  norm_num at hx

end AlexandrovGeometry
