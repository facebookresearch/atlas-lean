/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Geometry.Euclidean.Triangle
public import MathlibExt.Geometry.AlexandrovGeometry.FourPointComparison

/-!
# Euclidean affine spaces are Alexandrov of curvature `0`

This file shows the `κ = 0` comparison angle agrees with the Euclidean angle
and that Euclidean affine spaces satisfy the `Alex 0` four-point comparison.

## Main results
* `comparisonAngle_zero_eq_angle`: comparison angle equals Euclidean angle.
* `isAlex_zero_of_innerProductSpace`: Euclidean spaces are `Alex 0`.
-/

@[expose] public section

namespace AlexandrovGeometry

/-- In a Euclidean affine space, the `κ = 0` comparison angle at `p` equals
Mathlib's Euclidean angle. -/
theorem comparisonAngle_zero_eq_angle {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (p x y : P)
    (hx : x ≠ p) (hy : y ≠ p) :
    comparisonAngle 0 p x y = EuclideanGeometry.angle x p y := by
  have hb : 0 < dist p x := dist_pos.mpr (Ne.symm hx)
  have hc : 0 < dist p y := dist_pos.mpr (Ne.symm hy)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2x : 0 < 2 * dist p x := mul_pos h2pos hb
  have hpos : 0 < 2 * dist p x * dist p y := mul_pos h2x hc
  have hDne : 2 * dist p x * dist p y ≠ 0 := ne_of_gt hpos
  have hlaw := EuclideanGeometry.law_cos x p y
  have hcomm1 : dist x p = dist p x := dist_comm x p
  have hcomm2 : dist y p = dist p y := dist_comm y p
  rw [hcomm1, hcomm2] at hlaw
  have hcos : Real.cos (EuclideanGeometry.angle x p y) =
      (dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) /
        (2 * dist p x * dist p y) := by
    rw [eq_div_iff hDne]
    simp only [pow_two]
    have hring : Real.cos (EuclideanGeometry.angle x p y) *
        (2 * dist p x * dist p y) =
        2 * dist p x * dist p y * Real.cos (EuclideanGeometry.angle x p y) := by
      ring
    rw [hring]
    linarith [hlaw]
  have hnonneg : 0 ≤ EuclideanGeometry.angle x p y := by
    unfold EuclideanGeometry.angle
    exact InnerProductGeometry.angle_nonneg _ _
  have hle : EuclideanGeometry.angle x p y ≤ Real.pi := by
    unfold EuclideanGeometry.angle
    exact InnerProductGeometry.angle_le_pi _ _
  unfold comparisonAngle
  rw [modelAngle_zero_left]
  rw [← hcos]
  exact Real.arccos_cos hnonneg hle

/-- Every Euclidean affine space is `Alex 0`. -/
theorem isAlex_zero_of_innerProductSpace {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] :
    IsAlex 0 P := by
  intro p x1 x2 x3
  unfold FourPointComparison
  intro hdef
  have h12 : ModelAngleDefined 0 p x1 x2 := hdef.1
  have h23 : ModelAngleDefined 0 p x2 x3 := hdef.2.1
  unfold ModelAngleDefined at h12 h23
  have hp1 : 0 < dist p x1 := h12.2.1
  have hp2 : 0 < dist p x2 := h12.2.2
  have hp3 : 0 < dist p x3 := h23.2.2
  have hx1 : x1 ≠ p := Ne.symm (dist_pos.mp hp1)
  have hx2 : x2 ≠ p := Ne.symm (dist_pos.mp hp2)
  have hx3 : x3 ≠ p := Ne.symm (dist_pos.mp hp3)
  have c12 : comparisonAngle 0 p x1 x2 = EuclideanGeometry.angle x1 p x2 :=
    comparisonAngle_zero_eq_angle p x1 x2 hx1 hx2
  have c23 : comparisonAngle 0 p x2 x3 = EuclideanGeometry.angle x2 p x3 :=
    comparisonAngle_zero_eq_angle p x2 x3 hx2 hx3
  have c31 : comparisonAngle 0 p x3 x1 = EuclideanGeometry.angle x3 p x1 :=
    comparisonAngle_zero_eq_angle p x3 x1 hx3 hx1
  rw [c12, c23, c31]
  unfold EuclideanGeometry.angle
  have htri := InnerProductGeometry.angle_le_angle_add_angle (x2 -ᵥ p)
    (-(x3 -ᵥ p)) (x1 -ᵥ p)
  have hneg1 := InnerProductGeometry.angle_neg_right (x2 -ᵥ p) (x3 -ᵥ p)
  have hneg2 := InnerProductGeometry.angle_neg_right (x1 -ᵥ p) (x3 -ᵥ p)
  have hc1 := InnerProductGeometry.angle_comm (-(x3 -ᵥ p)) (x1 -ᵥ p)
  have hc2 := InnerProductGeometry.angle_comm (x1 -ᵥ p) (x3 -ᵥ p)
  have hc3 := InnerProductGeometry.angle_comm (x2 -ᵥ p) (x1 -ᵥ p)
  rw [hneg1, hc1, hneg2, hc2, hc3] at htri
  linarith [htri]

end AlexandrovGeometry
