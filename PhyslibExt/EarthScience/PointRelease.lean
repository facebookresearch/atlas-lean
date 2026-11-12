/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Point-release advection-diffusion-decay

For `t > 0`, the point-release kernel
`c(t, x) = M exp(-k t) exp(-(x - U t)^2 / (4 D t)) / √(4 π D t)` solves
the advection-diffusion-decay equation `c_t + U c_x = D c_xx - k c`, and
its total inventory is `∫_ℝ c(t, x) dx = M exp(-k t)`.

## i. Overview

The PDE is checked by differentiating in `t` and in `x` (iterated `deriv`
for `c_xx`) with the other variable held fixed. The inventory follows by
pulling out the `t`-dependent constants, translating `x ↦ x - U t`, and
using the Gaussian integral. No pointwise finite value at `t = 0` is
claimed; the distributional `t → 0` limit is not proved here.

## ii. Key results

- `EarthScience.point_release_solves_adr`: the kernel solves the PDE.
- `EarthScience.point_release_integral`: the inventory is `M exp(-k t)`.

## iii. Table of contents

- A. The point-release kernel

## iv. References

- `integral_gaussian` in `Mathlib/MeasureTheory/Integral/Gaussian.lean`
  (Mathlib).

## A. The point-release kernel
-/

@[expose] public section

open MeasureTheory

namespace EarthScience

/-- The point-release advection-diffusion-decay kernel
`c(t, x) = M exp(-k t) exp(-(x - U t)² / (4 D t)) / √(4 π D t)` solves
`c_t + U c_x = D c_xx - k c` for `t > 0` (derivatives written with
`deriv`, with the other variable held fixed). -/
theorem point_release_solves_adr (M D k U t x : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun t => M * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t)) t +
      U * deriv (fun x => M * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t)) x =
      D * deriv (fun x => deriv (fun x' => M * Real.exp (-k * t) *
        Real.exp (-(x' - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t)) x) x -
      k * (M * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t)) := by
  have hdt : (0:ℝ) < 4 * D * t := by positivity
  have hdt' : (4:ℝ) * D * t ≠ 0 := ne_of_gt hdt
  have hV : (0:ℝ) < 4 * Real.pi * D * t := by positivity
  have hV' : (4:ℝ) * Real.pi * D * t ≠ 0 := ne_of_gt hV
  have hS : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    positivity
  have hS2 : Real.sqrt (4 * Real.pi * D * t) ^ 2 = 4 * Real.pi * D * t :=
    Real.sq_sqrt (le_of_lt hV)
  -- inner x-exponent, at any point y
  have hg_all : ∀ y : ℝ, HasDerivAt (fun z : ℝ => -(z - U * t) ^ 2 / (4 * D * t))
      (-(2 * (y - U * t)) / (4 * D * t)) y := by
    intro y
    have hsq : HasDerivAt (fun z : ℝ => (z - U * t) ^ 2) (2 * (y - U * t)) y := by
      have h := ((hasDerivAt_id' y).sub_const (U * t)).pow 2
      convert h using 1
      ring
    exact hsq.neg.div_const _
  have he_all : ∀ y : ℝ, HasDerivAt (fun z : ℝ => Real.exp (-(z - U * t) ^ 2 / (4 * D * t)))
      (Real.exp (-(y - U * t) ^ 2 / (4 * D * t)) * (-(2 * (y - U * t)) / (4 * D * t))) y :=
    fun y => (hg_all y).exp
  -- first x-derivative, at any point y
  have hx : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => M * Real.exp (-k * t) * Real.exp (-(z - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t))
      (((M * Real.exp (-k * t)) *
        (Real.exp (-(y - U * t) ^ 2 / (4 * D * t)) * (-(2 * (y - U * t)) / (4 * D * t)))) /
        Real.sqrt (4 * Real.pi * D * t)) y := by
    intro y
    exact (HasDerivAt.const_mul _ (he_all y)).div_const _
  have hfun : (fun x => deriv (fun x' => M * Real.exp (-k * t) *
        Real.exp (-(x' - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t)) x)
      = (fun x => ((M * Real.exp (-k * t)) *
        (Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) * (-(2 * (x - U * t)) / (4 * D * t)))) /
        Real.sqrt (4 * Real.pi * D * t)) :=
    funext (fun y => (hx y).deriv)
  -- derivative of the linear factor q
  have hq : HasDerivAt (fun y : ℝ => -(2 * (y - U * t)) / (4 * D * t))
      ((-(2 * 1)) / (4 * D * t)) x := by
    have hlin : HasDerivAt (fun y : ℝ => 2 * (y - U * t)) (2 * 1) x :=
      HasDerivAt.const_mul _ ((hasDerivAt_id' x).sub_const (U * t))
    exact hlin.neg.div_const _
  -- second x-derivative
  have hprod : HasDerivAt
      (fun y : ℝ => Real.exp (-(y - U * t) ^ 2 / (4 * D * t)) * (-(2 * (y - U * t)) / (4 * D * t)))
      ((Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) * (-(2 * (x - U * t)) / (4 * D * t))) *
        (-(2 * (x - U * t)) / (4 * D * t)) +
        Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) * ((-(2 * 1)) / (4 * D * t))) x :=
    (he_all x).mul hq
  have hVxx : HasDerivAt
      (fun y : ℝ => ((M * Real.exp (-k * t)) *
        (Real.exp (-(y - U * t) ^ 2 / (4 * D * t)) * (-(2 * (y - U * t)) / (4 * D * t)))) /
        Real.sqrt (4 * Real.pi * D * t))
      (((M * Real.exp (-k * t)) *
        ((Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) * (-(2 * (x - U * t)) / (4 * D * t))) *
          (-(2 * (x - U * t)) / (4 * D * t)) +
          Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) * ((-(2 * 1)) / (4 * D * t)))) /
        Real.sqrt (4 * Real.pi * D * t)) x :=
    (HasDerivAt.const_mul _ hprod).div_const _
  -- t-derivative
  have hFt : HasDerivAt
      (fun z : ℝ => M * Real.exp (-k * z) * Real.exp (-(x - U * z) ^ 2 / (4 * D * z)) /
        Real.sqrt (4 * Real.pi * D * z))
      ((((0 * Real.exp (-k * t) + M * (Real.exp (-k * t) * -k)) *
        Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) +
        (M * Real.exp (-k * t)) *
          (Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) *
            (((-(2 * (x - U * t) * -U)) * (4 * D * t) - (-((x - U * t) ^ 2)) * (4 * D)) /
              (4 * D * t) ^ 2))) * Real.sqrt (4 * Real.pi * D * t) -
        (M * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t))) *
          ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t)))) /
        Real.sqrt (4 * Real.pi * D * t) ^ 2) t := by
    have hu : HasDerivAt (fun z : ℝ => x - U * z) (-U) t := by
      have h := HasDerivAt.const_sub x ((hasDerivAt_id' t).const_mul U)
      convert h using 1
      ring
    have hsq : HasDerivAt (fun z : ℝ => (x - U * z) ^ 2) (2 * (x - U * t) * -U) t := by
      have h := hu.pow 2
      convert h using 1
      ring
    have hn : HasDerivAt (fun z : ℝ => -((x - U * z) ^ 2)) (-(2 * (x - U * t) * -U)) t :=
      hsq.neg
    have hd : HasDerivAt (fun z : ℝ => 4 * D * z) (4 * D) t := by
      have h := (hasDerivAt_id' t).const_mul (4 * D)
      convert h using 1
      ring
    have hh : HasDerivAt (fun z : ℝ => -(x - U * z) ^ 2 / (4 * D * z))
        (((-(2 * (x - U * t) * -U)) * (4 * D * t) - (-((x - U * t) ^ 2)) * (4 * D)) /
          (4 * D * t) ^ 2) t :=
      hn.div hd hdt'
    have he2 : HasDerivAt (fun z : ℝ => Real.exp (-(x - U * z) ^ 2 / (4 * D * z)))
        (Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) *
          (((-(2 * (x - U * t) * -U)) * (4 * D * t) - (-((x - U * t) ^ 2)) * (4 * D)) /
            (4 * D * t) ^ 2)) t :=
      hh.exp
    have hj : HasDerivAt (fun z : ℝ => -k * z) (-k) t := by
      have h := (hasDerivAt_id' t).const_mul (-k)
      convert h using 1
      ring
    have he1 : HasDerivAt (fun z : ℝ => Real.exp (-k * z)) (Real.exp (-k * t) * -k) t :=
      hj.exp
    have hm : HasDerivAt (fun z : ℝ => 4 * Real.pi * D * z) (4 * Real.pi * D) t := by
      have h := (hasDerivAt_id' t).const_mul (4 * Real.pi * D)
      convert h using 1
      ring
    have hSder : HasDerivAt (fun z : ℝ => Real.sqrt (4 * Real.pi * D * z))
        ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))) t :=
      hm.sqrt hV'
    have hN : HasDerivAt
        (fun z : ℝ => M * Real.exp (-k * z) * Real.exp (-(x - U * z) ^ 2 / (4 * D * z)))
        ((0 * Real.exp (-k * t) + M * (Real.exp (-k * t) * -k)) *
          Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) +
          (M * Real.exp (-k * t)) *
            (Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) *
              (((-(2 * (x - U * t) * -U)) * (4 * D * t) - (-((x - U * t) ^ 2)) * (4 * D)) /
                (4 * D * t) ^ 2))) t :=
      ((hasDerivAt_const t M).mul he1).mul he2
    exact hN.div hSder hS
  have ex := (hx x).deriv
  have exx := hVxx.deriv
  have et := hFt.deriv
  rw [hfun, et, ex, exx]
  generalize hgen : Real.sqrt (4 * Real.pi * D * t) = S
  have hSS : S ≠ 0 := by rw [← hgen]; exact hS
  have hS2S : S ^ 2 = 4 * Real.pi * D * t := by rw [← hgen]; exact hS2
  rw [hS2S]
  field_simp
  rw [hS2S]
  ring


/-- The total inventory of the point-release kernel decays exactly at rate
`k`: `∫_ℝ c(t, x) dx = M exp(-k t)` for `t > 0`, `D > 0`. -/
theorem point_release_integral (M D k U t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    ∫ x : ℝ, M * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) /
      Real.sqrt (4 * Real.pi * D * t) = M * Real.exp (-k * t) := by
  have hdt : (0:ℝ) < 4 * D * t := by positivity
  have hdt' : (4:ℝ) * D * t ≠ 0 := ne_of_gt hdt
  have hS : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    positivity
  have hfactor : (fun x : ℝ => M * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) /
        Real.sqrt (4 * Real.pi * D * t))
      = (fun x : ℝ => (M * Real.exp (-k * t) / Real.sqrt (4 * Real.pi * D * t)) *
        Real.exp (-(x - U * t) ^ 2 / (4 * D * t))) := by
    funext x
    ring
  rw [hfactor, integral_const_mul]
  have hsub : ∫ x : ℝ, Real.exp (-(x - U * t) ^ 2 / (4 * D * t))
      = ∫ y : ℝ, Real.exp (-y ^ 2 / (4 * D * t)) :=
    integral_sub_right_eq_self (fun y => Real.exp (-y ^ 2 / (4 * D * t))) (U * t)
  rw [hsub]
  have hgauss : (fun y : ℝ => Real.exp (-y ^ 2 / (4 * D * t)))
      = (fun y => Real.exp (-(4 * D * t)⁻¹ * y ^ 2)) := by
    funext y
    congr 1
    field_simp
  rw [hgauss, integral_gaussian]
  have hsqrt : √(Real.pi / (4 * D * t)⁻¹) = Real.sqrt (4 * Real.pi * D * t) := by
    congr 1
    field_simp
  rw [hsqrt, div_mul_cancel₀ _ hS]

end EarthScience
