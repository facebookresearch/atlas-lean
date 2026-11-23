/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Geotherms: steady conductive geotherm with uniform heat production

For depth `d` in `[0, L]`, `k * T'' + H = 0` and `T(0) = Ts`, `T(L) = Tb`
give `T = Ts + [(Tb - Ts) / L + H * L / (2 * k)] * d - H * d ^ 2 / (2 * k)`.

## i. Overview

`L` is the layer thickness, `k > 0` the conductivity, `H` the constant
volumetric heat production, `Ts` the surface temperature, `Tb` the basal
temperature, depth `d` downward. The first derivative is the linear
gradient `(Tb - Ts) / L + H * L / (2 * k) - H * d / k`, the second
derivative is `-H / k`, so `k * T'' + H = 0`. The conductive flux in this
coordinate is `-k * T'`; the upward surface heat flux differs by sign.

## ii. Key results

- `EarthScience.geotherm_hasDerivAt`: first derivative of the geotherm.
- `EarthScience.geotherm_second_deriv`: second derivative and the ODE.
- `EarthScience.geotherm_boundary`: boundary values `T(0) = Ts`, `T(L) = Tb`.

## iii. Table of contents

- A. Conductive geotherm

## iv. References

- `HasDerivAt.const_mul`, `hasDerivAt_pow` in Mathlib.

## A. Conductive geotherm
-/

@[expose] public section

namespace EarthScience

/-- Conductive geotherm: first derivative of
`T(d) = Ts + [(Tb - Ts) / L + H * L / (2 * k)] * d - H * d ^ 2 / (2 * k)`. -/
theorem geotherm_hasDerivAt {Ts Tb L k H d : ℝ} :
    HasDerivAt (fun d => Ts + ((Tb - Ts) / L + H * L / (2 * k)) * d - H * d ^ 2 / (2 * k))
      ((Tb - Ts) / L + H * L / (2 * k) - H * d / k) d := by
  have hlin : HasDerivAt (fun d : ℝ => ((Tb - Ts) / L + H * L / (2 * k)) * d)
      ((Tb - Ts) / L + H * L / (2 * k)) d := by
    have h := HasDerivAt.const_mul ((Tb - Ts) / L + H * L / (2 * k)) (hasDerivAt_id d)
    simpa using h
  have hquad : HasDerivAt (fun d : ℝ => H * d ^ 2 / (2 * k)) (H * d / k) d := by
    have hp : HasDerivAt (fun d : ℝ => d ^ 2) (2 * d) d := by
      have h := hasDerivAt_pow 2 d
      simpa using h
    have h := HasDerivAt.const_mul (H / (2 * k)) hp
    have hfun : (fun d : ℝ => H * d ^ 2 / (2 * k)) = fun d => (H / (2 * k)) * d ^ 2 := by
      ext d
      ring
    have hder : H * d / k = (H / (2 * k)) * (2 * d) := by
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk0
        field_simp
    rw [hfun, hder]
    exact h
  have h := (HasDerivAt.const_add Ts hlin).sub hquad
  exact h

/-- Conductive geotherm: second derivative is `-H / k`, so `k * T'' + H = 0`. -/
theorem geotherm_second_deriv {Ts Tb L k H d : ℝ} (hk : 0 < k) :
    HasDerivAt (fun d => (Tb - Ts) / L + H * L / (2 * k) - H * d / k) (-H / k) d ∧
      k * (-H / k) + H = 0 := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun d : ℝ => H * d / k) (H / k) d := by
      have h := HasDerivAt.const_mul (H / k) (hasDerivAt_id d)
      have hfun : (fun d : ℝ => H * d / k) = fun d => (H / k) * d := by
        ext d
        ring
      have hder : H / k = (H / k) * 1 := by ring
      rw [hder, hfun]
      exact h
    have hC : HasDerivAt (fun _ : ℝ => (Tb - Ts) / L + H * L / (2 * k)) 0 d :=
      hasDerivAt_const d _
    have h := hC.sub h1
    have hder : -H / k = 0 - H / k := by ring
    rw [hder]
    exact h
  · have hk' : k ≠ 0 := ne_of_gt hk
    field_simp
    ring

/-- Conductive geotherm: boundary values `T(0) = Ts` and `T(L) = Tb`. -/
theorem geotherm_boundary {Ts Tb L k H : ℝ} (hL : 0 < L) (hk : 0 < k) :
    (Ts + ((Tb - Ts) / L + H * L / (2 * k)) * 0 - H * 0 ^ 2 / (2 * k)) = Ts ∧
      (Ts + ((Tb - Ts) / L + H * L / (2 * k)) * L - H * L ^ 2 / (2 * k)) = Tb := by
  refine ⟨by simp, ?_⟩
  have hL' : L ≠ 0 := ne_of_gt hL
  have hk' : k ≠ 0 := ne_of_gt hk
  have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk'
  field_simp
  ring

end EarthScience
