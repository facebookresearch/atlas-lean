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
  equation `ηtt = g * H * ηxx` and wave speed `√(gH)`. The spatial partial derivatives `ηx, ux` are
  given as `HasDerivAt` witnesses for the space slices, the PDEs are stated as `HasDerivAt` for the
  time slices, and mixed-derivative commutation and second-`x`-derivative differentiability are
  explicit hypotheses. The algebraic core `wave_eq_of_deriv_system` uses Lean's totalized `deriv`
  for the spatial partials; on its own it does not require the fields to be differentiable in `x`,
  so it is not the shallow-water PDE.

## ii. Key results

- `EarthScience.wave_eq_of_deriv_system`: the algebraic core, with totalized spatial `deriv`.
- `EarthScience.shallow_water_wave_eq`: the first-order system implies `∂ₜ²η = g * H * ∂ₓ²η`.
- `EarthScience.shallow_water_wave_speed`: `√(gH) > 0` and `(√(gH))² = g * H`.

## iii. Table of contents

- A. Wave equation
- B. Wave speed

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed., Cambridge University Press
  (2017), Chapter 3 (Shallow Water Systems and Isentropic Coordinates): the shallow-water
  equations, their linearization about a resting layer of depth `H`, and gravity waves with speed
  `√(gH)`.
- `HasDerivAt.deriv`, `deriv_const_mul`, `Filter.EventuallyEq.deriv_eq` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Wave equation -/

/-- Algebraic core of `shallow_water_wave_eq`, with the spatial partials written as Lean's
totalized `deriv`. If, for every `t, x`, `∂ₜη = -H ∂ₓu` and `∂ₜu = -g ∂ₓη` hold as `HasDerivAt`
statements for the time slices, the mixed-derivative commutation `∂ₜ∂ₓu = ∂ₓ∂ₜu` holds as a
`HasDerivAt` statement, and the second `x`-derivative of `η` is differentiable, then
`∂ₜ²η = g * H * ∂ₓ²η` at every `t, x`. Since `deriv` is `0` wherever a slice is not
differentiable, these hypotheses do not require `η t` or `u t` to be differentiable in `x`, so
they are not by themselves the shallow-water PDE; `shallow_water_wave_eq` adds that requirement. -/
lemma wave_eq_of_deriv_system {η u : ℝ → ℝ → ℝ} {H g : ℝ} (t x : ℝ)
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

/-- Linear 1D shallow water implies the wave equation. Suppose that, for every `t, x`, the
space slices of `η` and `u` have derivatives `ηx t x` and `ux t x` (as `HasDerivAt` statements),
the continuity equation `∂ₜη = -H ∂ₓu` and the momentum equation `∂ₜu = -g ∂ₓη` hold (as
`HasDerivAt` statements for the time slices), the mixed-derivative commutation `∂ₜ∂ₓu = ∂ₓ∂ₜu`
holds (as a `HasDerivAt` statement), and `ηx t` is differentiable. Then
`∂ₜ²η = g * H * ∂ₓ²η` at every `t, x`, where `deriv (fun s => η s x) t` is `∂ₜη(t, x)` and
`deriv (fun x' => ηx t x') x` is `∂ₓ²η(t, x)`. -/
theorem shallow_water_wave_eq {η u ηx ux : ℝ → ℝ → ℝ} {H g : ℝ} (t x : ℝ)
    (hηx : ∀ t x, HasDerivAt (fun x' => η t x') (ηx t x) x)
    (hux : ∀ t x, HasDerivAt (fun x' => u t x') (ux t x) x)
    (hcont : ∀ t x, HasDerivAt (fun t' => η t' x) (-H * ux t x) t)
    (hmom : ∀ t x, HasDerivAt (fun t' => u t' x) (-g * ηx t x) t)
    (hcomm : ∀ t x, HasDerivAt (fun t' => ux t' x)
      (deriv (fun x' => deriv (fun t' => u t' x') t) x) t)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun x' => ηx t x') x) :
    deriv (fun t' => deriv (fun s => η s x) t') t =
      g * H * deriv (fun x' => ηx t x') x := by
  have hηx' : ηx = fun t x => deriv (fun x' => η t x') x :=
    funext fun t => funext fun x => (hηx t x).deriv.symm
  have hux' : ux = fun t x => deriv (fun x' => u t x') x :=
    funext fun t => funext fun x => (hux t x).deriv.symm
  subst hηx' hux'
  exact wave_eq_of_deriv_system t x hcont hmom hcomm hdiff

/-! ## B. Wave speed -/

/-- Shallow-water wave speed: for `g, H > 0`, `Real.sqrt (g * H)` is
positive and its square is `g * H`. -/
theorem shallow_water_wave_speed {g H : ℝ} (hg : 0 < g) (hH : 0 < H) :
    0 < Real.sqrt (g * H) ∧ Real.sqrt (g * H) ^ 2 = g * H := by
  exact ⟨Real.sqrt_pos.2 (mul_pos hg hH), Real.sq_sqrt (le_of_lt (mul_pos hg hH))⟩

end EarthScience
