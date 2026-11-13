/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.EkmanPumping
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ekman pumping checks

Concrete consumers of `PhyslibExt.EarthScience.EkmanPumping`: the
stress field `tau0(x, y) = x * y`, `tau1(x, y) = x ^ 2 - y` at
`(x, y) = (1, 2)` with `rho0 * f = 2`, where the curl is `1` and the
divergence of the transport is `1 / 2`; the northern-hemisphere
upwelling and southern-hemisphere downwelling sign statements.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
partial derivatives of the concrete stress field are `d/dx tau1 = 2 * x`
and `d/dy tau0 = x`, so at `(1, 2)` the curl is `2 - 1 = 1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete stress field and hemispheric signs

## iv. References

- `PhyslibExt.EarthScience.EkmanPumping`
-/

/-- Partial derivative `d/dx tau1 = 2 * x` at `(1, 2)` for the concrete
stress field, divided by `rho0 * f = 2`: the value is `1`. -/
example : deriv (fun x' : ℝ => ((x' ^ 2 - (2 : ℝ)) / 2)) 1 = 1 := by
  have h : HasDerivAt (fun x' : ℝ => (x' ^ 2 - (2 : ℝ)) / 2) 1 1 := by
    have h1 := ((hasDerivAt_id' (x := (1 : ℝ))).pow 2).sub_const (2 : ℝ)
    have h2 := h1.div_const (2 : ℝ)
    convert h2 using 1
    norm_num
  exact h.deriv

/-- Partial derivative `d/dy tau0 = x = 1` at `(1, 2)` for the concrete
stress field, divided by `rho0 * f = 2` with a minus sign: `-1 / 2`. -/
example : deriv (fun y' : ℝ => -((1 : ℝ) * y' / 2)) 2 = -(1 / 2 : ℝ) := by
  have h : HasDerivAt (fun y' : ℝ => -((1 : ℝ) * y' / 2)) (-(1 / 2 : ℝ)) 2 := by
    have h1 := (hasDerivAt_id' (x := (2 : ℝ))).const_mul (1 : ℝ)
    have h2 := (h1.div_const (2 : ℝ)).neg
    convert h2 using 1
    norm_num
  exact h.deriv

/-- Divergence of the transport for the concrete stress field at
`(1, 2)`: `1 + (-1 / 2) = 1 / 2`, equal to `curl / (rho0 * f) = 1 / 2`. -/
example : deriv (fun x' : ℝ => ((x' ^ 2 - (2 : ℝ)) / 2)) 1 +
    deriv (fun y' : ℝ => -((1 : ℝ) * y' / 2)) 2 = (1 / 2 : ℝ) := by
  have h1 : deriv (fun x' : ℝ => ((x' ^ 2 - (2 : ℝ)) / 2)) 1 = 1 := by
    have h : HasDerivAt (fun x' : ℝ => (x' ^ 2 - (2 : ℝ)) / 2) 1 1 := by
      have h1 := ((hasDerivAt_id' (x := (1 : ℝ))).pow 2).sub_const (2 : ℝ)
      have h2 := h1.div_const (2 : ℝ)
      convert h2 using 1
      norm_num
    exact h.deriv
  have h2 : deriv (fun y' : ℝ => -((1 : ℝ) * y' / 2)) 2 = -(1 / 2 : ℝ) := by
    have h : HasDerivAt (fun y' : ℝ => -((1 : ℝ) * y' / 2)) (-(1 / 2 : ℝ)) 2 := by
      have h1 := (hasDerivAt_id' (x := (2 : ℝ))).const_mul (1 : ℝ)
      have h2 := (h1.div_const (2 : ℝ)).neg
      convert h2 using 1
      norm_num
    exact h.deriv
  rw [h1, h2]
  norm_num

/-- Northern hemisphere: with positive stress curl, the divergence is
positive (upwelling). This is a consumer of the sign theorem. -/
example (τ₀ τ₁ : ℝ → ℝ → ℝ) (ρ₀ f x y : ℝ) (hρ : 0 < ρ₀) (hf : 0 < f)
    (hτ₁x : HasDerivAt (fun x' => τ₁ x' y) (deriv (fun x' => τ₁ x' y) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ₀ x y') (deriv (fun y' => τ₀ x y') y) y)
    (hcurl : 0 < deriv (fun x' => τ₁ x' y) x - deriv (fun y' => τ₀ x y') y) :
    0 < deriv (fun x' => τ₁ x' y / (ρ₀ * f)) x +
      deriv (fun y' => -(τ₀ x y' / (ρ₀ * f))) y :=
  (EarthScience.ekman_pumping_sign τ₀ τ₁ ρ₀ f x y hρ hτ₁x hτ₀y hcurl).1 hf

/-- Southern hemisphere: with positive stress curl, the divergence is
negative (downwelling). This is a consumer of the sign theorem. -/
example (τ₀ τ₁ : ℝ → ℝ → ℝ) (ρ₀ f x y : ℝ) (hρ : 0 < ρ₀) (hf : f < 0)
    (hτ₁x : HasDerivAt (fun x' => τ₁ x' y) (deriv (fun x' => τ₁ x' y) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ₀ x y') (deriv (fun y' => τ₀ x y') y) y)
    (hcurl : 0 < deriv (fun x' => τ₁ x' y) x - deriv (fun y' => τ₀ x y') y) :
    deriv (fun x' => τ₁ x' y / (ρ₀ * f)) x +
      deriv (fun y' => -(τ₀ x y' / (ρ₀ * f))) y < 0 :=
  (EarthScience.ekman_pumping_sign τ₀ τ₁ ρ₀ f x y hρ hτ₁x hτ₀y hcurl).2 hf
