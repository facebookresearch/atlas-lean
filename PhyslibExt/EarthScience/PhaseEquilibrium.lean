/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Topology

/-!
# Clapeyron relation along a coexistence curve

## i. Overview

Along a `C1` coexistence curve with chemical potentials `μ1 = μ2`
and `dμᵢ = vᵢ dp - sᵢ dT`, the Clapeyron relation is
`dp / dT = (s2 - s1) / (v2 - v1)` when `v2 ≠ v1`. The curve's existence
is hypothesised through the derivative data, not derived here.
`T` is absolute, `v`, `s` consistently molar or mass-specific, and the
critical point (where `v2 = v1`) is excluded. The latent-heat form
`dp / dT = L / (T * (v2 - v1))` with `L = T * (s2 - s1)` is also recorded.

## ii. Key results

- `EarthScience.clapeyron_dp_dT`: `dp / dT = (s2 - s1) / (v2 - v1)`.
- `EarthScience.clapeyron_latentHeat_form`: the latent-heat form.

## iii. Table of contents

- A. Clapeyron relation
- B. Latent-heat form

## iv. References

- Donald A. McQuarrie and John D. Simon, *Physical Chemistry: A Molecular
  Approach* (University Science Books, 1997), Chapter 23, Phase Equilibria,
  Sections 23.3-23.4: coexistence is `μ_α = μ_β`; from `G = n μ` and
  `(∂G/∂p)_T = V`, `(∂G/∂T)_p = -S` the chemical-potential differential is
  `dμ = v dp - s dT`; the Clapeyron equation is `dp/dT = Δs/Δv`, and with
  `ΔH = T Δs` at fixed `T` the latent-heat form is `dp/dT = ΔH / (T Δv)`.
  Here `L = T * (s2 - s1)` is that molar latent heat (enthalpy change),
  with phase `2` minus phase `1` in both differences.
- `HasDerivAt.sub` / `HasDerivAt.unique` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Clapeyron relation along a coexistence curve: with
`dμᵢ = vᵢ dp - sᵢ dT` and equal chemical potentials near the point
(`μ1 =ᶠ[𝓝 t] μ2`, so `μ1 - μ2` has derivative `0` there),
`dp/dT = (s2 - s1) / (v2 - v1)` when `v2 ≠ v1` and `dT ≠ 0`. Here
`dp`, `dT` are the derivatives of the pressure and temperature along
the curve at the point. -/
theorem clapeyron_dp_dT {mu1 mu2 : ℝ → ℝ} {v1 v2 s1 s2 dp dT : ℝ} {t : ℝ}
    (hv : v2 - v1 ≠ 0) (hdT : dT ≠ 0)
    (hmu1 : HasDerivAt mu1 (v1 * dp - s1 * dT) t)
    (hmu2 : HasDerivAt mu2 (v2 * dp - s2 * dT) t)
    (hcoex : mu1 =ᶠ[𝓝 t] mu2) :
    dp / dT = (s2 - s1) / (v2 - v1) := by
  have hsub := hmu1.sub hmu2
  have heq : HasDerivAt (fun t => mu1 t - mu2 t) 0 t := by
    have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
    have hEq : (fun t => mu1 t - mu2 t) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
      hcoex.mono fun x hx => by simp [hx]
    exact h0.congr_of_eventuallyEq hEq
  have heq' : HasDerivAt (mu1 - mu2) 0 t := heq
  have hzero := hsub.unique heq'
  have hlin : dp * (v2 - v1) = (s2 - s1) * dT := by linear_combination -hzero
  rw [div_eq_div_iff hdT hv]
  exact hlin

/-- Latent-heat form, as a corollary of `clapeyron_dp_dT`: with
`L = T * (s2 - s1)` (the molar latent heat, `ΔH = T Δs`) and `T ≠ 0`,
`dp / dT = L / (T * (v2 - v1))`. -/
theorem clapeyron_latentHeat_form {mu1 mu2 : ℝ → ℝ} {v1 v2 s1 s2 dp dT T L : ℝ}
    {t : ℝ} (hv : v2 - v1 ≠ 0) (hdT : dT ≠ 0) (hT : T ≠ 0)
    (hmu1 : HasDerivAt mu1 (v1 * dp - s1 * dT) t)
    (hmu2 : HasDerivAt mu2 (v2 * dp - s2 * dT) t)
    (hcoex : mu1 =ᶠ[𝓝 t] mu2) (hL : L = T * (s2 - s1)) :
    dp / dT = L / (T * (v2 - v1)) := by
  have hmain := clapeyron_dp_dT hv hdT hmu1 hmu2 hcoex
  rw [hmain, hL]
  exact (mul_div_mul_left _ _ hT).symm

end EarthScience
