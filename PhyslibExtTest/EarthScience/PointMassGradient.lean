/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PointMassGradient

/-!
# Point-mass gradient checks

Concrete consumers of `PhyslibExt.EarthScience.PointMassGradient`: the
one-dimensional case `G = M = 1`, `x = 5`, where the gradient is
`(1 / 125) • 5 = 1 / 25` and the inward inner product is `-(1 / 25) * 5
= -1 / 5 < 0`, and the zero-mass boundary of the gradient formula.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
concrete case exercises both conjuncts at a point away from the origin;
the zero-mass case applies the gradient formula where the inwardness
hypotheses fail.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. One-dimensional concrete case
- B. Gradient without a sign condition

## iv. References

- `PhyslibExt.EarthScience.PointMassGradient`
-/

/-- Public shape of the point-mass gradient theorem. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G M : ℝ} {x : E} (hx : x ≠ 0) (hG : 0 < G) (hM : 0 < M) :
    HasFDerivAt (fun y => -G * M / ‖y‖)
      (InnerProductSpace.toDual ℝ E ((G * M / ‖x‖ ^ 3) • x)) x ∧
    inner ℝ (-((G * M / ‖x‖ ^ 3) • x)) x < 0 :=
  EarthScience.pointMass_gradient_inward hx hG hM

/-- Concrete case `G = M = 1`, `x = 5` in `ℝ`: the gradient is
`1 / 25` and the acceleration points inward. -/
example :
    HasFDerivAt (fun y : ℝ => -(1 : ℝ) * 1 / ‖y‖)
      (InnerProductSpace.toDual ℝ ℝ (((1 : ℝ) * 1 / ‖(5 : ℝ)‖ ^ 3) • (5 : ℝ))) (5 : ℝ) ∧
    inner ℝ (-(((1 : ℝ) * 1 / ‖(5 : ℝ)‖ ^ 3) • (5 : ℝ))) (5 : ℝ) < 0 :=
  EarthScience.pointMass_gradient_inward (by norm_num) (by norm_num) (by norm_num)

/-- The inward inner product at `x = 5` is `-1 / 5`. -/
example : inner ℝ (-(((1 : ℝ) * 1 / ‖(5 : ℝ)‖ ^ 3) • (5 : ℝ))) (5 : ℝ) = -(1 / 5 : ℝ) := by
  have h := (EarthScience.pointMass_gradient_inward (G := (1 : ℝ)) (M := (1 : ℝ))
    (x := (5 : ℝ)) (by norm_num) (by norm_num) (by norm_num)).2
  have hinner : inner ℝ (-(((1 : ℝ) * 1 / ‖(5 : ℝ)‖ ^ 3) • (5 : ℝ))) (5 : ℝ)
      = -(1 * 1 / ‖(5 : ℝ)‖) := by
    rw [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rw [hinner]
  norm_num

/-! ## B. Gradient without a sign condition -/

/-- Public shape of the gradient theorem: only `x ≠ 0` is assumed. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G M : ℝ} {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y => -G * M / ‖y‖) ((G * M / ‖x‖ ^ 3) • x) x :=
  EarthScience.hasGradientAt_pointMass_potential hx

/-- Concrete gradient at `x = 5` in `ℝ` with `G = M = 1`: `(1 / 125) • 5 = 1 / 25`. -/
example : HasGradientAt (fun y : ℝ => -(1 : ℝ) * 1 / ‖y‖) (1 / 25) 5 := by
  have h := EarthScience.hasGradientAt_pointMass_potential (G := (1 : ℝ)) (M := (1 : ℝ))
    (x := (5 : ℝ)) (by norm_num)
  convert h using 1
  norm_num

/-- Zero-mass boundary: the potential is identically zero and its gradient is zero. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y : E => -(2 : ℝ) * 0 / ‖y‖) 0 x := by
  have h := EarthScience.hasGradientAt_pointMass_potential (G := 2) (M := 0) hx
  simpa using h
