 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Diffusion-limited droplet growth

## i. Overview

In the diffusion-limited droplet model `r * r' = K*S` with constant
`K >= 0, S` and `r > 0`, `r(t) = sqrt(r0^2 + 2*K*S*t)` has
`r(t)^2 = r0^2 + 2*K*S*t`, `(r^2)' = 2*K*S`, and `r' = K*S / r(t)`
when `r(t) > 0`. Curvature, solute, and ventilation effects are
ignored; there is no zero-radius continuation.

## ii. Key results

- `EarthScience.radius_sq`: `(r(t))^2 = r0^2 + 2*K*S*t`.
- `EarthScience.radius_sq_hasDerivAt`: `(r^2)' = 2*K*S` where the argument is positive.
- `EarthScience.radius_hasDerivAt`: `r' = K*S / r(t)` when `r(t) > 0`.
- `EarthScience.no_supersaturation`: `S = 0` keeps `r = r0`.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


set_option linter.unusedVariables false in
/-- Diffusion-limited droplet growth: with `r(t) = sqrt(r0^2 + 2*K*S*t)`,
the squared radius satisfies `r(t)^2 = r0^2 + 2*K*S*t`. -/
theorem radius_sq {r0 K S t : ℝ} (hr0 : 0 < r0) (hK : 0 ≤ K)
    (h : 0 ≤ r0 ^ 2 + 2 * K * S * t) :
    (Real.sqrt (r0 ^ 2 + 2 * K * S * t)) ^ 2 = r0 ^ 2 + 2 * K * S * t := by
  exact Real.sq_sqrt h

set_option linter.unusedVariables false in
/-- Diffusion-limited droplet growth: the squared radius has derivative
`2*K*S` at every `t`. -/
theorem radius_sq_hasDerivAt {r0 K S : ℝ} (hr0 : 0 < r0) (hK : 0 ≤ K) (t : ℝ)
    (hpos : 0 < r0 ^ 2 + 2 * K * S * t) :
    HasDerivAt (fun t => (Real.sqrt (r0 ^ 2 + 2 * K * S * t)) ^ 2) (2 * K * S) t := by
  have hinner : HasDerivAt (fun t => r0 ^ 2 + 2 * K * S * t) (2 * K * S) t := by
    have h1 := (hasDerivAt_id t).const_mul (2 * K * S)
    rw [mul_one] at h1
    exact h1.const_add (r0 ^ 2)
  have hcont : ContinuousAt (fun t => r0 ^ 2 + 2 * K * S * t) t := hinner.continuousAt
  have heq : (fun t => (Real.sqrt (r0 ^ 2 + 2 * K * S * t)) ^ 2)
      =ᶠ[nhds t] (fun t => r0 ^ 2 + 2 * K * S * t) := by
    filter_upwards [hcont.eventually (Ioi_mem_nhds hpos)] with x hx
    exact Real.sq_sqrt (le_of_lt hx)
  exact hinner.congr_of_eventuallyEq heq

set_option linter.unusedVariables false in
/-- Diffusion-limited droplet growth: at a time with `r(t) > 0`,
`HasDerivAt r (K*S / r(t)) t`, i.e. `r(t) * r'(t) = K*S`. -/
theorem radius_hasDerivAt {r0 K S : ℝ} (hr0 : 0 < r0) (hK : 0 ≤ K) (t : ℝ)
    (hr : 0 < Real.sqrt (r0 ^ 2 + 2 * K * S * t)) :
    HasDerivAt (fun t => Real.sqrt (r0 ^ 2 + 2 * K * S * t))
      (K * S / Real.sqrt (r0 ^ 2 + 2 * K * S * t)) t := by
  have hne : Real.sqrt (r0 ^ 2 + 2 * K * S * t) ≠ 0 := ne_of_gt hr
  have harg : r0 ^ 2 + 2 * K * S * t ≠ 0 := by
    intro hzero
    rw [hzero, Real.sqrt_zero] at hr
    exact lt_irrefl 0 hr
  have hinner : HasDerivAt (fun t => r0 ^ 2 + 2 * K * S * t) (2 * K * S) t := by
    have h1 := (hasDerivAt_id t).const_mul (2 * K * S)
    rw [mul_one] at h1
    exact h1.const_add (r0 ^ 2)
  have h := hinner.sqrt harg
  have heq : 2 * K * S / (2 * Real.sqrt (r0 ^ 2 + 2 * K * S * t))
      = K * S / Real.sqrt (r0 ^ 2 + 2 * K * S * t) := by
    field_simp
  rwa [heq] at h

set_option linter.unusedVariables false in
/-- No supersaturation (`S = 0`): the radius stays `r0`. -/
theorem no_supersaturation {r0 K t : ℝ} (hr0 : 0 < r0) (hK : 0 ≤ K) :
    Real.sqrt (r0 ^ 2 + 2 * K * (0 : ℝ) * t) = r0 := by
  have harg : r0 ^ 2 + 2 * K * (0 : ℝ) * t = r0 ^ 2 := by ring
  rw [harg]
  exact Real.sqrt_sq (le_of_lt hr0)


end EarthScience
