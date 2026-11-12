/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Ring

/-!
# Shallow-water waves, tides, and sea level

## i. Overview

Linear 1D shallow water, `ηt + H * ux = 0` and `ut + g * ηx = 0` with `g, H > 0`, implies the wave
  equation `ηtt = g * H * ηxx` and wave speed `√(gH)`. The PDEs are stated as `HasDerivAt` for time
  slices, mixed-derivative commutation and second-`x`-derivative differentiability are explicit
  hypotheses, and `deriv` of a slice is the partial derivative.

## ii. Key results

- `EarthScience.shallow_water_wave_eq`: the first-order system implies `∂ₜ²η = g * H * ∂ₓ²η`.
- `EarthScience.shallow_water_wave_speed`: `√(gH) > 0` and `(√(gH))² = g * H`.

## iii. Table of contents

- A. Wave equation
- B. Wave speed

## iv. References

- `HasDerivAt.deriv`, `deriv_const_mul`, `Filter.EventuallyEq.deriv_eq` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Linear 1D shallow water implies the wave equation. If `η, u` satisfy,
for every `t, x`, the continuity equation
`∂ₜη = -H ∂ₓu` and momentum equation `∂ₜu = -g ∂ₓη` (as `HasDerivAt`
statements for the time slices), the mixed-derivative commutation
`∂ₜ∂ₓu = ∂ₓ∂ₜu` (as a `HasDerivAt` statement), and the second `x`-derivative
of `η` is differentiable, then `∂ₜ²η = g * H * ∂ₓ²η` at every `t, x`.
Here `deriv (fun s => η s x) t` is `∂ₜη(t, x)`, etc. -/
theorem shallow_water_wave_eq {η u : ℝ → ℝ → ℝ} {H g : ℝ} (t x : ℝ)
    (hcont : ∀ t x, HasDerivAt (fun t' => η t' x)
      (-H * deriv (fun x' => u t x') x) t)
    (hmom : ∀ t x, HasDerivAt (fun t' => u t' x)
      (-g * deriv (fun x' => η t x') x) t)
    (hcomm : ∀ t x, HasDerivAt (fun t' => deriv (fun x' => u t' x') x)
      (deriv (fun x' => deriv (fun t' => u t' x') t) x) t)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun x' => deriv (fun x'' => η t x'') x') x) :
    deriv (fun t' => deriv (fun s => η s x) t') t =
      g * H * deriv (fun x' => deriv (fun x'' => η t x'') x') x := by
  have hcont' : ∀ t', deriv (fun s => η s x) t' = -H * deriv (fun x' => u t' x') x :=
    fun t' => (hcont t' x).deriv
  have hmom' : ∀ x', deriv (fun t' => u t' x') t = -g * deriv (fun x'' => η t x'') x' :=
    fun x' => (hmom t x').deriv
  have hcomm' : deriv (fun t' => deriv (fun x' => u t' x') x) t =
      deriv (fun x' => deriv (fun t' => u t' x') t) x :=
    (hcomm t x).deriv
  have hdiffU : DifferentiableAt ℝ (fun t' => deriv (fun x' => u t' x') x) t :=
    (hcomm t x).differentiableAt
  have heq1 : Filter.EventuallyEq (nhds t) (fun t' => deriv (fun s => η s x) t')
      (fun t' => -H * deriv (fun x' => u t' x') x) :=
    Filter.Eventually.of_forall hcont'
  have heq2 : Filter.EventuallyEq (nhds x) (fun x' => deriv (fun t' => u t' x') t)
      (fun x' => -g * deriv (fun x'' => η t x'') x') :=
    Filter.Eventually.of_forall hmom'
  rw [heq1.deriv_eq, deriv_const_mul _ hdiffU, hcomm', heq2.deriv_eq,
    deriv_const_mul _ (hdiff t x)]
  ring

/-- Shallow-water wave speed: for `g, H > 0`, `Real.sqrt (g * H)` is
positive and its square is `g * H`. -/
theorem shallow_water_wave_speed {g H : ℝ} (hg : 0 < g) (hH : 0 < H) :
    0 < Real.sqrt (g * H) ∧ Real.sqrt (g * H) ^ 2 = g * H := by
  exact ⟨Real.sqrt_pos.2 (mul_pos hg hH), Real.sq_sqrt (le_of_lt (mul_pos hg hH))⟩

end EarthScience
