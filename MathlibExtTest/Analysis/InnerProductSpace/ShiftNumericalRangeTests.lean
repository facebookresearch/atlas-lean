/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ShiftNumericalRange
public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-!
# Tests for the numerical range of the unilateral shift

* The numerical ranges of the forward and backward shifts are the open
  unit disc: they contain `0`, `1 / 2`, `-1 / 2`, `I / 2`, but not `1`,
  `-1`, or `2`.
* The geometric vector for `u = 1 / 2` is a unit vector whose forward-shift
  quadratic form is `1 / 2` and whose backward-shift quadratic form is `1 / 2`.
-/

open Set Filter Topology Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.ShiftNumericalRange
open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted

namespace MathlibExtTest.Analysis.InnerProductSpace.ShiftNumericalRangeTests

/-- `‖(1 / 2 : ℂ)‖ = 1 / 2 < 1`. -/
private theorem norm_half_lt_one : ‖(1 / 2 : ℂ)‖ < 1 := by
  rw [Complex.norm_div, norm_one, Complex.norm_two]
  norm_num

/-- `0` is in the numerical range of the forward shift. -/
example : (0 : ℂ) ∈ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM]
  exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)

/-- `1 / 2` is in the numerical range of the forward shift. -/
example : (1 / 2 : ℂ) ∈ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right]
  exact norm_half_lt_one

/-- `-1 / 2` is in the numerical range of the forward shift. -/
example : (-1 / 2 : ℂ) ∈ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right]
  rw [Complex.norm_div, norm_neg, norm_one, Complex.norm_two]
  norm_num

/-- `I / 2` is in the numerical range of the forward shift. -/
example : (Complex.I / 2 : ℂ) ∈ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right]
  rw [Complex.norm_div, Complex.norm_I, Complex.norm_two]
  norm_num

/-- `1` is not in the numerical range of the forward shift: the range is
open, while `1` is on the boundary. -/
example : (1 : ℂ) ∉ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right]
  simp

/-- `-1` is not in the numerical range of the forward shift. -/
example : (-1 : ℂ) ∉ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right]
  simp

/-- `2` is not in the numerical range of the forward shift. -/
example : (2 : ℂ) ∉ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right]
  simp

/-- `1 / 2` is in the numerical range of the backward shift. -/
example : (1 / 2 : ℂ) ∈ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right]
  exact norm_half_lt_one

/-- `0` is in the numerical range of the backward shift. -/
example : (0 : ℂ) ∈ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM]
  exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)

/-- `-1 / 2` is in the numerical range of the backward shift. -/
example : (-1 / 2 : ℂ) ∈ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right]
  rw [Complex.norm_div, norm_neg, norm_one, Complex.norm_two]
  norm_num

/-- `I / 2` is in the numerical range of the backward shift. -/
example : (Complex.I / 2 : ℂ) ∈ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right]
  rw [Complex.norm_div, Complex.norm_I, Complex.norm_two]
  norm_num

/-- `1` is not in the numerical range of the backward shift. -/
example : (1 : ℂ) ∉ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right]
  simp

/-- `-1` is not in the numerical range of the backward shift. -/
example : (-1 : ℂ) ∉ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right]
  simp

/-- `2` is not in the numerical range of the backward shift. -/
example : (2 : ℂ) ∉ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right]
  simp

/-- The nonreal boundary point `I` is excluded for both shifts. -/
example : (Complex.I : ℂ) ∉ numericalRange fwdShiftCLM := by
  rw [numericalRange_fwdShiftCLM, Metric.mem_ball, dist_zero_right, Complex.norm_I]
  norm_num

example : (Complex.I : ℂ) ∉ numericalRange bwdShiftCLM := by
  rw [numericalRange_bwdShiftCLM, Metric.mem_ball, dist_zero_right, Complex.norm_I]
  norm_num

/-- The geometric vector for `u = 1 / 2` is a unit vector. -/
example : ‖geom (1 / 2 : ℂ)‖ = 1 :=
  norm_geom norm_half_lt_one

/-- A coordinate unit vector satisfies the strict bound, including when `k ≠ 0`. -/
example (k : ℕ) :
    ∑' n, ‖(lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ)) n‖ *
      ‖(lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ)) (n + 1)‖ < 1 := by
  apply sum_norm_mul_succ_lt_one
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one]

/-- The geometric vector at zero is a unit vector. -/
example : ‖geom (0 : ℂ)‖ = 1 :=
  norm_geom (by simp)

/-- Outside the disc the geometric vector is zero, as in its unrestricted definition. -/
example : geom (2 : ℂ) = 0 := by
  have hsqrt : Real.sqrt (1 - ‖(2 : ℂ)‖ ^ 2) = 0 := by
    apply Real.sqrt_eq_zero_of_nonpos
    rw [Complex.norm_two]
    norm_num
  apply lp.ext
  funext n
  simp only [geom_apply, hsqrt]
  simp

/-- The forward-shift quadratic form at the geometric vector for `1 / 2`
is `1 / 2`. -/
example : ⟪fwdShiftCLM (geom (1 / 2 : ℂ)), geom (1 / 2 : ℂ)⟫_ℂ = (1 / 2 : ℂ) :=
  quadForm_fwd_geom norm_half_lt_one

/-- The backward-shift quadratic form at the geometric vector for the real
scalar `1 / 2` is `1 / 2` (conjugation fixes real scalars). -/
example : ⟪bwdShiftCLM (geom (((1 / 2 : ℝ) : ℂ))), geom (((1 / 2 : ℝ) : ℂ))⟫_ℂ
    = ((1 / 2 : ℝ) : ℂ) := by
  have hnorm : ‖(((1 / 2 : ℝ) : ℂ))‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    norm_num
  have h := quadForm_bwd_geom hnorm
  rwa [Complex.conj_ofReal] at h

/-- The numerical range of the forward shift is the open unit disc. -/
example : numericalRange (LpShiftOperator.shiftCLM (𝕜 := ℂ)) = Metric.ball (0 : ℂ) 1 :=
  numericalRange_fwdShiftCLM

/-- The canonical forward shift realizes the nonreal geometric parameter itself. -/
example : ⟪LpShiftOperator.shiftCLM (geom (Complex.I / 2)), geom (Complex.I / 2)⟫_ℂ =
    Complex.I / 2 := by
  apply quadForm_fwd_geom
  rw [Complex.norm_div, Complex.norm_I, Complex.norm_two]
  norm_num

/-- The canonical backward shift conjugates a nonreal geometric parameter. -/
example : ⟪LpShiftOperator.backwardCLM (geom (Complex.I / 2)), geom (Complex.I / 2)⟫_ℂ =
    -Complex.I / 2 := by
  have hnorm : ‖(Complex.I / 2 : ℂ)‖ < 1 := by
    rw [Complex.norm_div, Complex.norm_I, Complex.norm_two]
    norm_num
  have hbackward : LpShiftOperator.backwardCLM (𝕜 := ℂ) = bwdShiftCLM := rfl
  rw [hbackward, quadForm_bwd_geom hnorm]
  simp [map_ofNat]

/-- The numerical range of the backward shift is the open unit disc. -/
example : numericalRange (LpShiftOperator.backwardCLM (𝕜 := ℂ)) = Metric.ball (0 : ℂ) 1 :=
  numericalRange_bwdShiftCLM

#print axioms numericalRange_fwdShiftCLM

#print axioms numericalRange_bwdShiftCLM

end MathlibExtTest.Analysis.InnerProductSpace.ShiftNumericalRangeTests
